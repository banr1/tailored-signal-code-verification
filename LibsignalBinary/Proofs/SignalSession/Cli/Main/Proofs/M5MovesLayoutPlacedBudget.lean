/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5IfacePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MovesLayoutPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded `memcpy` Helper for `main` M5 Moves (Block `617`)

Lifts `sessionMemcpyRegionBudgetSpec` on Block `617` to `step_memcpy_region_fs_placed`, preserving
`VmPreserved` so `A.pool lim st` transports across `main`'s M5 `memcpy` calls.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MovesLayoutPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack memcpyName sessionMemcpyRegionSpec withStack)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (LsCodeInv main_call_rocl)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)

namespace M5MovesHelpers

abbrev sepWP_seq_placed_frame :=
  @CryptoVerification.SignalSession.Cli.MainHops.M5MovesHelpers.sepWP_seq_placed_frame

theorem main_sessionMemcpyRegionFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsFsPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl (withStack sessionMemcpyRegionBudgetSpec extHookStack).keepsFs) :=
  AllocFsSitesPlacedBudget.AllocContractsFsPlaced.session_memcpy_region_rocl hA
    (prog := lsProg_617 H) (i := 617) extHookStack (by decide) (by decide)

/-- Step a `bl memcpy` call in `main` under
`(withStack sessionMemcpyRegionBudgetSpec extHookStack).keepsFs`, preserving `VmPreserved`,
`fs`, `trace`, `sp`, `CalleeSavedPreserved`, and `CodeOk`, and copying `src ↦ₛ bs` into
`memRegion dst bs.length`. -/
theorem step_memcpy_region_fs_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {prog : Program} {memcpyTarget fsp retPc ret dst src : BitVec 64} {bs : List (BitVec 8)}
    {fs0 : FsState} {tr0 : List TraceEvent}
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hmc : subroutine_ok prog memcpyTarget
      (withLsRoCl lsmpl (withStack sessionMemcpyRegionBudgetSpec extHookStack).keepsFs))
    (hinv : CodeOk s.mem)
    (hpc : s.pc = memcpyTarget)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hal : s.spAligned = true)
    (hlr : s.readReg64 .lr = retPc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hfs : s.fs = fs0)
    (htr : s.trace = tr0)
    (hP : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack ∗ F)
    (hk : ∀ sm : State,
      CodeOk sm.mem →
      sm.pc = retPc →
      sm.status = .Running →
      sm.sp = fsp →
      CalleeSavedPreserved s sm →
      VmPreserved s sm →
      sm.fs = fs0 →
      sm.trace = tr0 →
      SepWPp prog ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt fsp extHookStack ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  refine main_call_rocl (dst, src, bs) hmc hinv hpc hrun hal hlr
    (F := F)
    (hP := ?_)
    (hpanic := fun _ _ _ hp => by
      dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
        sessionMemcpyRegionSpec] at hp
      exact (not_satisfies_false_sepConj hp).elim)
    (hexit := fun _ _ _ _ he => by
      dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
        sessionMemcpyRegionSpec] at he
      exact not_satisfies_false_sepConj he)
    (hoom := fun _ _ _ ho => by
      dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
        sessionMemcpyRegionSpec] at ho
      exact (not_satisfies_false_sepConj ho).elim)
    (hnext := ?_)
  · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp]
    refine Entails.trans hP ?_
    have hpure :
        ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ =
        (emp : SepProp) := by
      simp [hx0, hx1, hx2]
    rw [hpure, emp_sepConj]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    rw [hsp]
    have hpure_pull :
        ((⌜sm.fs = s.fs⌝ ∗
          ((⌜VmPreserved s sm⌝ ∗
            (⌜sm.readReg64 .x0 = dst ∧ sm.trace = s.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs))) ∗
            stackAt fsp extHookStack)) ∗ F) =
        ⌜sm.fs = s.fs⌝ ∗
          (⌜VmPreserved s sm⌝ ∗
            (⌜sm.readReg64 .x0 = dst ∧ sm.trace = s.trace⌝ ∗
              (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt fsp extHookStack ∗ F))) := by
      sep_ac_rfl
    rw [hpure_pull]
    refine SepWPp.pure_elim fun hfsm => ?_
    refine SepWPp.pure_elim fun hvm => ?_
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    exact hk sm hinv_m hpcm hrunm hspm hcsm hvm (hfsm.trans hfs) (htrm.trans htr)

end M5MovesHelpers

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MovesLayoutPlacedBudget
