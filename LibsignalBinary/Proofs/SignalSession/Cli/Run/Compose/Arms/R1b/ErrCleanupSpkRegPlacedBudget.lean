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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkRegPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Budget-Threaded SPK and Registration Buffer Error Cleanup (`2b24 → 2b28 → 2b78 → 2bf0`)

Verifies `r1b_cleanup_2b78_placed`, `r1b_cleanup_2b28_placed`, `r1b_cleanup_2b24_placed`, and their
`RejectKPlacedEnv` wrappers (`FreeOnlyEvs`) on Block `579` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkRegPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced Init1Data PanicK RejectKind r1b_CodeOk r1b_ErrCtxPlaced
   r1b_SpePayload r1b_SpePayload_zext_r9_r22 r1b_StackBounds r1b_bind_state_placed
   r1b_cell64_cons r1b_cells2_region8_to_24 r1b_cells2_to_region16 r1b_errCommon
   r1b_errCore r1b_errLow4 r1b_fold_low4 r1b_fsp_align r1b_region16_to_cells
   rejectMem runFsp runPcPlaced runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (r1b_cleanup_2bf0_placed r1b_errCommon_atState_eq sepWP_with_vm_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

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

private theorem r1b_seq_lscro_oom [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcrl h

private theorem r1b_rejoin_188_placed (fsp regCap regPtr : BitVec 64) :
    memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
      ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ⊢
      memRegion (fsp + 0x188#64) 48 := by
  have h1a0 : ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ⊢
      memRegion (fsp + 0x1a0#64) 24 := by
    have ha : fsp + 0x1a8#64 = (fsp + 0x1a0#64) + 8#64 := by bv_omega
    rw [ha]; exact r1b_cell64_cons regPtr (by decide)
  have h198 : ((fsp + 0x198#64) ↦₆₄ regCap) ∗ memRegion (fsp + 0x1a0#64) 24 ⊢
      memRegion (fsp + 0x198#64) 32 := by
    have ha : fsp + 0x1a0#64 = (fsp + 0x198#64) + 8#64 := by bv_omega
    rw [ha]; exact r1b_cell64_cons regCap (by decide)
  have h188 : memRegion (fsp + 0x188#64) 16 ∗ memRegion (fsp + 0x198#64) 32 ⊢
      memRegion (fsp + 0x188#64) 48 := by
    have ha : fsp + 0x198#64 = (fsp + 0x188#64) + 16#64 := by bv_omega
    rw [ha, show (48 : Nat) = 16 + 32 from rfl,
      ProofLib.memRegion_split (fsp + 0x188#64) 16 32 (by decide)]
    exact Entails.refl _
  exact Entails.trans (sepConj_mono_right (Entails.trans (sepConj_mono_right h1a0) h198)) h188

private theorem r1b_rejoin_168_placed (fsp spkPtr spkCap : BitVec 64) :
    ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (fsp + 0x178#64) 8 ⊢ memRegion (fsp + 0x168#64) 24 := by
  have ha8 : fsp + 0x170#64 = (fsp + 0x168#64) + 8#64 := by bv_omega
  have ha16 : fsp + 0x178#64 = (fsp + 0x168#64) + 16#64 := by bv_omega
  rw [ha8, ha16]
  exact r1b_cells2_region8_to_24 (fsp + 0x168#64) spkPtr spkCap

set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2b78_cap0_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regPtr regLen : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2b78)
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
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A.repAlloc 0#64 regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ 0#64) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2b78#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2bf0#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm2 hsm2 hinv_m2 => ?_
    rw [← hsm2] at hvm
    rw [← A.pool_transport lim st s sm2 hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x2bf0 := {
      st := {
        pc := by simp only [hsm2, wp_norm, arm64_norm]
        run := by simp only [hsm2, wp_norm, arm64_norm, hrun]
        sp := by simpa only [hsm2, wp_norm, arm64_norm] using hsp
        fp := by simpa only [hsm2, wp_norm, arm64_norm] using hfp
        inv := hinv_m2
        vregs := by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hvregs
        spAligned := hsp0
      }
      x19 := by simpa only [hsm2, wp_norm, arm64_norm] using hc.x19
      x20 := by simpa only [hsm2, wp_norm, arm64_norm] using hc.x20
      x21 := by simpa only [hsm2, wp_norm, arm64_norm] using hc.x21
      trace := by simpa only [hsm2, wp_norm, arm64_norm] using hc.trace
      hist := ⟨by simpa only [hsm2, wp_norm, arm64_norm] using hc.hist.1,
        by simpa only [hsm2, wp_norm, arm64_norm] using hc.hist.2⟩
      ans := hc.ans
    }
    have hr12 : sm2.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by
      simp only [hsm2, wp_norm, arm64_norm]
    have hr9 : sm2.readReg64 (.gpr 9#5) =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (s.readReg64 (.gpr 10#5))) := by
      simp only [hsm2, wp_norm, arm64_norm]
    have hr23 : sm2.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by
      simp only [hsm2, wp_norm, arm64_norm]
    have hr27 : sm2.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
      simp only [hsm2, wp_norm, arm64_norm]
    have hr16 : sm2.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by
      simp only [hsm2, wp_norm, arm64_norm]
    have hr14 : sm2.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by
      simp only [hsm2, wp_norm, arm64_norm]
    have hr15 : sm2.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by
      simp only [hsm2, wp_norm, arm64_norm]
    have hr28 : sm2.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
      simp only [hsm2, wp_norm, arm64_norm]
    have hr22 : sm2.readReg64 (.gpr 22#5) =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (s.readReg64 (.gpr 2#5))) := by
      simp only [hsm2, wp_norm, arm64_norm]
    refine sepWPp_weaken_pre ?_ (r1b_cleanup_2bf0_placed (st := st) hh hdrop hbnd hc_m hpanic hrej)
    rw [hr12, hr9, hr23, hr27, hr16, hr14, hr15, hr28, hr22]
    rw [r1b_errCommon_atState_eq, herrCore, r1b_fold_low4]
    dsimp only [fsp]
    have hdrop_reg : ownedBytes A.repAlloc 0#64 regPtr regLen regBs ∗ anyHeap ⊢ anyHeap :=
      entails_anyHeap _
    refine Entails.trans (Entails.of_eq (show _ =
      r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
        (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
        (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
        (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
        (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
      (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm2 ∗
        (ownedBytes A.repAlloc 0#64 regPtr regLen regBs ∗ anyHeap)) ∗
      r1b_errLow4 (runFsp s0) ∗
      memRegion (runFsp s0 + 0x168#64) 24 ∗
      (memRegion (runFsp s0 + 0x188#64) 16 ∗ ((runFsp s0 + 0x198#64) ↦₆₄ 0#64) ∗
        ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (runFsp s0 + 0x1a8#64) 16) ∗
      memRegion (runFsp s0 + 0x4d0#64) 48 by sep_ac_rfl)) ?_
    exact sepConj_mono r1b_SpePayload_zext_r9_r22
      (sepConj_mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hdrop_reg)))
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (r1b_rejoin_188_placed (runFsp s0) 0#64 regPtr)))))
  )

set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2b78_capNe_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr regLen : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2b78)
    (hcap : regCap ≠ 0#64)
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
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hcap_f : (regCap == 0#64) = false := beq_false_of_ne hcap
  have hsplit168 : memRegion (fsp + 0x168#64) 24 =
      memRegion (fsp + 0x168#64) 16 ∗ ∃∗ v178 : BitVec 64, (fsp + 0x178#64) ↦₆₄ v178 := by
    rw [show (24 : Nat) = 16 + 8 from rfl, ProofLib.memRegion_split (fsp + 0x168#64) 16 8 (by decide),
      show fsp + 0x168#64 + 16#64 = fsp + 0x178#64 from by bv_omega, ProofLib.memRegion_eight]
  rw [hsplit168, sepExists_sepConj_right,
    r1b_region16_to_cells (fsp + 0x188#64), r1b_region16_to_cells (fsp + 0x1a8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v178 => SepWPp.exists_elim fun v188 =>
    SepWPp.exists_elim fun v190 => SepWPp.exists_elim fun v1a8 =>
    SepWPp.exists_elim fun v1b0 => ?_
  have ho190 : fsp + 0x188#64 + 8#64 = fsp + 0x190#64 := by bv_omega
  have ho1b0 : fsp + 0x1a8#64 + 8#64 = fsp + 0x1b0#64 := by bv_omega
  rw [ho190, ho1b0]
  change s.pc = (blkPl_579).base + 0x2b78#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hsm_run : sm.status = .Running := by simp only [hsm, wp_norm, arm64_norm, hrun]
    have hsm_sp0 : sm.sp = runFsp s0 := by simpa only [hsm, wp_norm, arm64_norm] using hsp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 :=
      by simpa only [hsm, wp_norm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2bb8 := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_a0 : sm.readReg64 .x0 = regPtr := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_a1 : sm.readReg64 .x1 = regCap := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_a2 : sm.readReg64 .x2 = 1#64 := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_x19 : sm.readReg64 (.gpr 19#5) = g.stores :=
      by simpa only [hsm, wp_norm, arm64_norm] using hc.x19
    have hsm_x20 : sm.readReg64 (.gpr 20#5) = g.res :=
      by simpa only [hsm, wp_norm, arm64_norm] using hc.x20
    have hsm_r21 : sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 27#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 14#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r25 : sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 12#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r26 : sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 28#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 16#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 15#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_fs : sm.fs = s.fs := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_tr : sm.trace = s.trace := by simp only [hsm, wp_norm, arm64_norm]
    clear hsm
    rw [← hfsp_eq]
    refine sepWPp_weaken_pre (P' :=
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
        (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
            (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
            (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
            (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
            (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
          errCore ∗ anyHeap ∗ r1b_errLow4 (runFsp s0) ∗
          memRegion (runFsp s0 + 0x168#64) 16 ∗ ((runFsp s0 + 0x178#64) ↦₆₄ s.readReg64 (.gpr 10#5)) ∗
          ((runFsp s0 + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗ ((runFsp s0 + 0x190#64) ↦₆₄ v1a8) ∗
          ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
          ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
          memRegion (runFsp s0 + 0x4d0#64) 48)) ?_ ?_
    · exact Entails.of_eq (by sep_ac_rfl)
    refine r1b_call_dealloc_ownedBytes_placed (Q := Q) (cap := regCap) (ptr := regPtr)
      (len := regLen) (bs := regBs)
      hh hbnd hinv_m hsm_pc hsm_run
      hsm_sp0 hsm_fp hsm_vr hsp0 hsm_lr
      hsm_a0 hsm_a1 hsm_a2
      hcap hpanic ?_
    intro s1 hin1 hcs1 hfs1 htr1
    rw [hfsp_eq]
    have hpc1 := hin1.pc; have hrun1 := hin1.run
    have hsp1 : s1.sp = fsp := hin1.sp
    have hfp1 := hin1.fp; have hinv1 := hin1.inv; have hvregs1 := hin1.vregs
    change s1.pc = (blkPl_579).base + 0x2bb8#64 at hpc1
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2bf0#64) hinv1
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
      rw [← hsm2] at hvm2
      rw [← A.pool_transport lim _ s1 sm2 hvm2]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rcases hcs1 with ⟨hc19, hc20, hc21, hc22, hc24, hc25, hc26, hc27, hc28, hc29, _, _⟩
      have htr2 : sm2.trace = s.trace := by simp only [hsm2, wp_norm, arm64_norm]; exact htr1.trans hsm_tr
      have hfs2 : sm2.fs = s.fs := by simp only [hsm2, wp_norm, arm64_norm]; exact hfs1.trans hsm_fs
      have hc_m2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x2bf0 := {
        st := {
          pc := by simp only [hsm2, wp_norm, arm64_norm]
          run := by simp only [hsm2, wp_norm, arm64_norm, hrun1]
          sp := by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp
          fp := by simpa only [hsm2, wp_norm, arm64_norm] using hfp1
          inv := hinv2
          vregs := by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hvregs1
          spAligned := hsp0
        }
        x19 := by simp only [hsm2, wp_norm, arm64_norm, hc19, hsm_x19]
        x20 := by simp only [hsm2, wp_norm, arm64_norm, hc20, hsm_x20]
        x21 := by simp only [hsm2, wp_norm, arm64_norm]; exact hc.x21
        trace := htr2 ▸ hc.trace
        hist := ⟨by rw [hfs2]; exact hc.hist.1, by rw [htr2]; exact hc.hist.2⟩
        ans := hc.ans
      }
      have hr12 : sm2.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc26, hsm_r25]
      have hr9 : sm2.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 10#5) := by
        simp only [hsm2, wp_norm, arm64_norm]
      have hr23 : sm2.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by
        simp only [hsm2, wp_norm, arm64_norm]
      have hr27 : sm2.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc21, hsm_r21]
      have hr16 : sm2.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc28, hsm_r27]
      have hr14 : sm2.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc24, hsm_r23]
      have hr15 : sm2.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc29, hsm_r28]
      have hr28 : sm2.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc27, hsm_r26]
      have hr22 : sm2.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 2#5) := by
        simp only [hsm2, wp_norm, arm64_norm]
      clear hsm2
      have hre168 : memRegion (fsp + 0x168#64) 16 ∗ ((fsp + 0x178#64) ↦₆₄ s.readReg64 (.gpr 10#5)) ⊢
          memRegion (fsp + 0x168#64) 24 := by
        rw [show (24 : Nat) = 16 + 8 from rfl, ProofLib.memRegion_split (fsp + 0x168#64) 16 8 (by decide),
          show fsp + 0x168#64 + 16#64 = fsp + 0x178#64 from by bv_omega]
        exact sepConj_mono_right (pointsTo64_entails_memRegion _ _)
      have hre188 : ((fsp + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗ ((fsp + 0x190#64) ↦₆₄ v1a8) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
          ((fsp + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ⊢ memRegion (fsp + 0x188#64) 48 := by
        have ha1 : fsp + 0x190#64 = (fsp + 0x188#64) + 8#64 := by bv_omega
        have ha2 : fsp + 0x1b0#64 = (fsp + 0x1a8#64) + 8#64 := by bv_omega
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗ ((fsp + 0x190#64) ↦₆₄ v1a8)) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          (((fsp + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
            ((fsp + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5))) by sep_ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono (by rw [ha1]; exact r1b_cells2_to_region16 _ _ _)
            (sepConj_mono_right (sepConj_mono_right
              (by rw [ha2]; exact r1b_cells2_to_region16 _ _ _))))
          (r1b_rejoin_188_placed fsp regCap regPtr)
      refine sepWPp_weaken_pre ?_
        (r1b_cleanup_2bf0_placed (st := M.stepEvents (rustDeallocEvents regCap.toNat 1) st)
          hh hdrop hbnd hc_m2 hpanic fun sf2 evs2 hfo2 hrej2 => ?_)
      · rw [hr12, hr9, hr23, hr27, hr16, hr14, hr15, hr28, hr22]
        rw [r1b_errCommon_atState_eq, herrCore, r1b_fold_low4]
        dsimp only [fsp] at hre168 hre188 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
            (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
            (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
            (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
            (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
          (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents regCap.toNat 1) st) sm2 ∗ anyHeap) ∗
          r1b_errLow4 (runFsp s0) ∗
          (memRegion (runFsp s0 + 0x168#64) 16 ∗ ((runFsp s0 + 0x178#64) ↦₆₄ s.readReg64 (.gpr 10#5))) ∗
          (((runFsp s0 + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗ ((runFsp s0 + 0x190#64) ↦₆₄ v1a8) ∗
            ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
            ((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
            ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5))) ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 by sep_ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono hre168 (sepConj_mono_left hre188))))
      · rw [← M.stepEvents_append]
        exact hrej sf2 (rustDeallocEvents regCap.toNat 1 ++ evs2)
          (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 regCap.toNat) hfo2) hrej2
    )
  )

theorem r1b_cleanup_2b78_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr regLen : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2b78)
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
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  by_cases hcap : regCap = 0#64
  · subst hcap; exact r1b_cleanup_2b78_cap0_placed hh hdrop hbnd hc hpanic hrej
  · exact r1b_cleanup_2b78_capNe_placed hh hdrop hbnd hc hcap hpanic hrej

set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2b28_cap0_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2b28)
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
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A.repAlloc 0#64 spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ 0#64) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2b28#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2b78#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b78 := {
      st := {
        pc := by simp only [hsm, wp_norm, arm64_norm]
        run := by simp only [hsm, wp_norm, arm64_norm, hrun]
        sp := by simpa only [hsm, wp_norm, arm64_norm] using hc.st.sp
        fp := by simpa only [hsm, wp_norm, arm64_norm] using hfp
        inv := hinv_m
        vregs := by simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
        spAligned := hsp0
      }
      x19 := by simpa only [hsm, wp_norm, arm64_norm] using hc.x19
      x20 := by simpa only [hsm, wp_norm, arm64_norm] using hc.x20
      x21 := by simpa only [hsm, wp_norm, arm64_norm] using hc.x21
      trace := by simpa only [hsm, wp_norm, arm64_norm] using hc.trace
      hist := ⟨by simpa only [hsm, wp_norm, arm64_norm] using hc.hist.1,
        by simpa only [hsm, wp_norm, arm64_norm] using hc.hist.2⟩
      ans := hc.ans
    }
    have hr12 : sm.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr10 : sm.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 10#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr16 : sm.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr14 : sm.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr15 : sm.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr2 : sm.readReg64 (.gpr 2#5) = s.readReg64 (.gpr 2#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2b78_placed (st := st) (regCap := regCap) (regPtr := regPtr)
        (regLen := regLen) (regBs := regBs)
        hh hdrop hbnd hc_m hpanic hrej)
    rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28, hr2]
    rw [r1b_errCommon_atState_eq, herrCore, r1b_fold_low4]
    dsimp only [fsp]
    have hdrop_spk : ownedBytes A.repAlloc 0#64 spkPtr spkLen spkBs ∗ anyHeap ⊢ anyHeap :=
      entails_anyHeap _
    refine Entails.trans (Entails.of_eq (show _ =
      r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
        (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
        (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
        (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
        (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
      ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
      (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
        (ownedBytes A.repAlloc 0#64 spkPtr spkLen spkBs ∗ anyHeap)) ∗
      r1b_errLow4 (runFsp s0) ∗
      (((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ 0#64) ∗
        memRegion (runFsp s0 + 0x178#64) 8) ∗
      memRegion (runFsp s0 + 0x188#64) 16 ∗ ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗
      ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (runFsp s0 + 0x1a8#64) 16 ∗
      memRegion (runFsp s0 + 0x4d0#64) 48 by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hdrop_spk)))
        (sepConj_mono_right (sepConj_mono_left (r1b_rejoin_168_placed (runFsp s0) spkPtr 0#64)))))
  )

set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2b28_capNe_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2b28)
    (hcap : spkCap ≠ 0#64)
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
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hcap_f : (spkCap == 0#64) = false := beq_false_of_ne hcap
  rw [r1b_region16_to_cells (fsp + 0x188#64), r1b_region16_to_cells (fsp + 0x1a8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v188 => SepWPp.exists_elim fun v190 =>
    SepWPp.exists_elim fun v1a8 => SepWPp.exists_elim fun v1b0 => ?_
  have ho190 : fsp + 0x188#64 + 8#64 = fsp + 0x190#64 := by bv_omega
  have ho1b0 : fsp + 0x1a8#64 + 8#64 = fsp + 0x1b0#64 := by bv_omega
  rw [ho1b0]; rw [ho190]
  change s.pc = (blkPl_579).base + 0x2b28#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hsm_run : sm.status = .Running := by simp only [hsm, wp_norm, arm64_norm, hrun]
    have hsm_sp0 : sm.sp = runFsp s0 := by simpa only [hsm, wp_norm, arm64_norm] using hc.st.sp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 :=
      by simpa only [hsm, wp_norm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2b58 := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_a0 : sm.readReg64 .x0 = spkPtr := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_a1 : sm.readReg64 .x1 = spkCap := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_a2 : sm.readReg64 .x2 = 1#64 := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_x19 : sm.readReg64 (.gpr 19#5) = g.stores :=
      by simpa only [hsm, wp_norm, arm64_norm] using hc.x19
    have hsm_x20 : sm.readReg64 (.gpr 20#5) = g.res :=
      by simpa only [hsm, wp_norm, arm64_norm] using hc.x20
    have hsm_x21 : sm.readReg64 (.gpr 21#5) = d.meG.name.cap :=
      by simpa only [hsm, wp_norm, arm64_norm] using hc.x21
    have hsm_r22 : sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 10#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 14#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r25 : sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 12#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r26 : sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 16#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 15#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_fs : sm.fs = s.fs := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_tr : sm.trace = s.trace := by simp only [hsm, wp_norm, arm64_norm]
    clear hsm
    rw [← hfsp_eq]
    refine sepWPp_weaken_pre (P' :=
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
        (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
            (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
            (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
            (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
            (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
          ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
          errCore ∗ anyHeap ∗ r1b_errLow4 (runFsp s0) ∗
          ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (runFsp s0 + 0x178#64) 8 ∗
          ((runFsp s0 + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗
          ((runFsp s0 + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5)) ∗
          ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
          ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
          memRegion (runFsp s0 + 0x4d0#64) 48)) ?_ ?_
    · exact Entails.of_eq (by sep_ac_rfl)
    refine r1b_call_dealloc_ownedBytes_placed (Q := Q) (cap := spkCap) (ptr := spkPtr)
      (len := spkLen) (bs := spkBs)
      hh hbnd hinv_m hsm_pc hsm_run
      hsm_sp0 hsm_fp hsm_vr hsp0 hsm_lr
      hsm_a0 hsm_a1 hsm_a2
      hcap hpanic ?_
    intro s1 hin1 hcs1 hfs1 htr1
    rw [hfsp_eq]
    have hpc1 := hin1.pc; have hrun1 := hin1.run
    have hsp1 : s1.sp = fsp := hin1.sp
    have hfp1 := hin1.fp; have hinv1 := hin1.inv; have hvregs1 := hin1.vregs
    change s1.pc = (blkPl_579).base + 0x2b58#64 at hpc1
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2b78#64) hinv1
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
      rw [← hsm2] at hvm2
      rw [← A.pool_transport lim _ s1 sm2 hvm2]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rcases hcs1 with ⟨hc19, hc20, hc21, hc22, hc24, hc25, hc26, hc27, hc28, hc29, _, _⟩
      have htr2 : sm2.trace = s.trace := by simp only [hsm2, wp_norm, arm64_norm]; exact htr1.trans hsm_tr
      have hfs2 : sm2.fs = s.fs := by simp only [hsm2, wp_norm, arm64_norm]; exact hfs1.trans hsm_fs
      have hc_m2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x2b78 := {
        st := {
          pc := by simp only [hsm2, wp_norm, arm64_norm]
          run := by simp only [hsm2, wp_norm, arm64_norm, hrun1]
          sp := by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp
          fp := by simpa only [hsm2, wp_norm, arm64_norm] using hfp1
          inv := hinv2
          vregs := by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hvregs1
          spAligned := hsp0
        }
        x19 := by simp only [hsm2, wp_norm, arm64_norm, hc19, hsm_x19]
        x20 := by simp only [hsm2, wp_norm, arm64_norm, hc20, hsm_x20]
        x21 := by simp only [hsm2, wp_norm, arm64_norm, hc21, hsm_x21]
        trace := htr2 ▸ hc.trace
        hist := ⟨by rw [hfs2]; exact hc.hist.1, by rw [htr2]; exact hc.hist.2⟩
        ans := hc.ans
      }
      have hr12 : sm2.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc26, hsm_r25]
      have hr10 : sm2.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 10#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc22, hsm_r22]
      have hr23 : sm2.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by
        simp only [hsm2, wp_norm, arm64_norm]
      have hr27 : sm2.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc28, hsm_r27]
      have hr16 : sm2.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc27, hsm_r26]
      have hr14 : sm2.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc24, hsm_r23]
      have hr15 : sm2.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc29, hsm_r28]
      have hr28 : sm2.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
        simp only [hsm2, wp_norm, arm64_norm]
      have hr2 : sm2.readReg64 (.gpr 2#5) = s.readReg64 (.gpr 2#5) := by
        simp only [hsm2, wp_norm, arm64_norm]
      clear hsm2
      have hre188 : ((fsp + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗
          ((fsp + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5)) ⊢ memRegion (fsp + 0x188#64) 16 := by
        have ha1 : fsp + 0x190#64 = (fsp + 0x188#64) + 8#64 := by bv_omega
        rw [ha1]; exact r1b_cells2_to_region16 _ _ _
      have hre1a8 : ((fsp + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
          ((fsp + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ⊢ memRegion (fsp + 0x1a8#64) 16 := by
        have ha2 : fsp + 0x1b0#64 = (fsp + 0x1a8#64) + 8#64 := by bv_omega
        rw [ha2]; exact r1b_cells2_to_region16 _ _ _
      refine sepWPp_weaken_pre ?_
        (r1b_cleanup_2b78_placed (st := M.stepEvents (rustDeallocEvents spkCap.toNat 1) st)
          (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
          hh hdrop hbnd hc_m2 hpanic fun sf2 evs2 hfo2 hrej2 => ?_)
      · rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28, hr2]
        rw [r1b_errCommon_atState_eq, herrCore, r1b_fold_low4]
        dsimp only [fsp] at hre188 hre1a8 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
            (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
            (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
            (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
            (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
          ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
          (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents spkCap.toNat 1) st) sm2 ∗ anyHeap) ∗
          r1b_errLow4 (runFsp s0) ∗
          (((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
            memRegion (runFsp s0 + 0x178#64) 8) ∗
          (((runFsp s0 + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗
            ((runFsp s0 + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5))) ∗
          ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
          (((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
            ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5))) ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 by sep_ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (r1b_rejoin_168_placed (runFsp s0) spkPtr spkCap)
            (sepConj_mono hre188
              (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left hre1a8))))))))
      · rw [← M.stepEvents_append]
        exact hrej sf2 (rustDeallocEvents spkCap.toNat 1 ++ evs2)
          (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 spkCap.toNat) hfo2) hrej2
    )
  )

theorem r1b_cleanup_2b28_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2b28)
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
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  by_cases hcap : spkCap = 0#64
  · subst hcap; exact r1b_cleanup_2b28_cap0_placed hh hdrop hbnd hc hpanic hrej
  · exact r1b_cleanup_2b28_capNe_placed hh hdrop hbnd hc hcap hpanic hrej

theorem r1b_cleanup_2b24_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v188 spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2b24)
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
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2b24#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2b28#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b28 := {
      st := {
        pc := by simp only [hsm, wp_norm, arm64_norm]
        run := by simp only [hsm, wp_norm, arm64_norm, hrun]
        sp := by simpa only [hsm, wp_norm, arm64_norm] using hc.st.sp
        fp := by simpa only [hsm, wp_norm, arm64_norm] using hfp
        inv := hinv_m
        vregs := by simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
        spAligned := hsp0
      }
      x19 := by simpa only [hsm, wp_norm, arm64_norm] using hc.x19
      x20 := by simpa only [hsm, wp_norm, arm64_norm] using hc.x20
      x21 := by simpa only [hsm, wp_norm, arm64_norm] using hc.x21
      trace := by simpa only [hsm, wp_norm, arm64_norm] using hc.trace
      hist := ⟨by simpa only [hsm, wp_norm, arm64_norm] using hc.hist.1,
        by simpa only [hsm, wp_norm, arm64_norm] using hc.hist.2⟩
      ans := hc.ans
    }
    have hr12 : sm.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr10 : sm.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 10#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr16 : sm.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr14 : sm.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr15 : sm.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr2 : sm.readReg64 (.gpr 2#5) = v188 := by simp only [hsm, wp_norm, arm64_norm]
    have hre : ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ⊢
        memRegion (fsp + 0x188#64) 16 := by
      have ha : fsp + 0x190#64 = (fsp + 0x188#64) + 8#64 := by bv_omega
      rw [ha]; exact r1b_cell64_cons v188 (by decide)
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2b28_placed (st := st)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
        hh hdrop hbnd hc_m hpanic hrej)
    rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28, hr2, r1b_errCommon_atState_eq, herrCore,
      r1b_fold_low4]
    dsimp only [fsp] at hre ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
        (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
        (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
        (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
        (s.readReg64 (.gpr 28#5)) v188 ∗
      ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
      ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
      (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗ anyHeap) ∗
      r1b_errLow4 (runFsp s0) ∗
      ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (runFsp s0 + 0x178#64) 8 ∗
      (((runFsp s0 + 0x188#64) ↦₆₄ v188) ∗ memRegion (runFsp s0 + 0x190#64) 8) ∗
      ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
      memRegion (runFsp s0 + 0x1a8#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hre))))))))
  )

/-! ## `RejectKPlacedEnv` Wrappers -/

theorem r1b_cleanup_2b78_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr regLen : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2b78)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2b78_placed hh hdrop hbnd hc hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

theorem r1b_cleanup_2b28_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2b28)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2b28_placed hh hdrop hbnd hc hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

theorem r1b_cleanup_2b24_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v188 spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2b24)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2b24_placed hh hdrop hbnd hc hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkRegPlacedBudget
