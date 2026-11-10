/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFdsStrClone
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec

/-!
# K-Route `String::clone` File-Descriptor Hook Bridges

Proves that `h2k_strCloneGhostHookK` preserves `State.fs`, lifts its budget contract
through `withFdsGe3Closed` and `withFds`, and assembles the 12-field `RunHooksPlaced`
bundle over `withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks IsFsC cliGhostExterns cliGhostExterns_stringClone_some)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk (cliRunHooksPlaced_of_ghost)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (hookOk_withFdsGe3Closed_of_fs_eq withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (cliGhostAllocHooks_withFds cliGhostSpqrAllocHooks_withFds withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFdsStrClone
  (hookOk_stringCloneBudget_withFds hookSat_stringCloneBudget_withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
  (h2kb_hole2_hFs h2kb_hole2_hG h2kb_hole2_hGSpqr h2kb_stringCloneBudget_hookSat)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_ghFixedK h2k_strCloneGhostHookK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open VerifiedLibraries (mallocngLib)

/-! ## `State.fs` Preservation -/

/-- `h2k_strCloneGhostHookK` preserves `State.fs` across active, fallback, and exception outcomes. -/
theorem h2k_strCloneGhostHookK_fs_eq [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (s0 : State) :
    (h2k_strCloneGhostHookK mpl mmpl s0).fs = s0.fs := by
  classical
  unfold h2k_strCloneGhostHookK
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.1
    · rfl
  · rfl

theorem hookOk_withFdsGe3Closed_strCloneGhostHookK [LibsignalPlacement] {α : Type}
    {mpl mmpl : MultiPlacement} {spec : Spec α}
    (hok : HookOk (h2k_strCloneGhostHookK mpl mmpl) spec) :
    HookOk (h2k_strCloneGhostHookK mpl mmpl) (withFdsGe3Closed spec) :=
  hookOk_withFdsGe3Closed_of_fs_eq (h2k_strCloneGhostHookK_fs_eq mpl mmpl) hok

/-- Any function resolved at `lsStringCloneSym` in `cliGhostExterns (h2k_ghFixedK mpl mmpl) base` preserves `State.fs`. -/
theorem h2k_ghFixedK_stringClone_fs_eq [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (base : LibsignalHooks)
    (fn : State → State)
    (hfn : cliGhostExterns (h2k_ghFixedK mpl mmpl) base lsStringCloneSym = some fn)
    (s0 : State) :
    (fn s0).fs = s0.fs := by
  rw [cliGhostExterns_stringClone_some (h2k_ghFixedK mpl mmpl) base rfl] at hfn
  injection hfn with hEq
  subst hEq
  exact h2k_strCloneGhostHookK_fs_eq mpl mmpl s0

/-! ## Lifting to `withFdsGe3Closed` -/

/-- `HookOk` for `h2k_strCloneGhostHookK` against `stringCloneBudgetSpec` over `fineHookRustCliAllocBudget`. -/
theorem h2kb_stringCloneBudget_hookOk
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_strCloneGhostHookK mpl mmpl)
      (stringCloneBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  obtain ⟨fn, hfn, hOk⟩ := h2kb_stringCloneBudget_hookSat mpl mmpl hLs hMm (fun _ => none) γ tp
  rw [cliGhostExterns_stringClone_some (h2k_ghFixedK mpl mmpl) (fun _ => none) rfl] at hfn
  injection hfn with hEq
  subst hEq
  exact hOk

/-- `HookOk` for `h2k_strCloneGhostHookK` lifted to `withFdsGe3Closed`. -/
theorem h2kb_stringCloneBudget_withFdsGe3Closed_hookOk
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_strCloneGhostHookK mpl mmpl)
      (withFdsGe3Closed
        (stringCloneBudgetSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)) :=
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  hookOk_withFdsGe3Closed_of_fs_eq
    (h2k_strCloneGhostHookK_fs_eq mpl mmpl)
    (h2kb_stringCloneBudget_hookOk mpl mmpl hLs hMm γ tp)

/-- `HookSat` for `lsStringCloneSym` under `withFdsGe3Closed (stringCloneBudgetSpec fineCostModel A0 cliBudgetLimits)`. -/
theorem h2kb_stringCloneBudget_withFdsGe3Closed_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsStringCloneSym
      (withFdsGe3Closed
        (stringCloneBudgetSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)) :=
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  ⟨h2k_strCloneGhostHookK mpl mmpl,
   cliGhostExterns_stringClone_some (h2k_ghFixedK mpl mmpl) base rfl,
   h2kb_stringCloneBudget_withFdsGe3Closed_hookOk mpl mmpl hLs hMm γ tp⟩

/-! ## Lifting to `withFds` and `RunHooksPlaced` -/

/-- `HookOk` for `h2k_strCloneGhostHookK` under `withFds`. -/
theorem h2kb_stringCloneBudget_withFds_hookOk
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_strCloneGhostHookK mpl mmpl)
      (stringCloneBudgetSpec fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits) :=
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  hookOk_stringCloneBudget_withFds
    (h2kb_stringCloneBudget_hookOk mpl mmpl hLs hMm γ tp)
    (h2k_strCloneGhostHookK_fs_eq mpl mmpl)

/-- `HookSat` for `lsStringCloneSym` under `stringCloneBudgetSpec fineCostModel (withFds A0) cliBudgetLimits`. -/
theorem h2kb_stringCloneBudget_withFds_hookSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (base : LibsignalHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) base) lsStringCloneSym
      (stringCloneBudgetSpec fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits) :=
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  ⟨h2k_strCloneGhostHookK mpl mmpl,
   cliGhostExterns_stringClone_some (h2k_ghFixedK mpl mmpl) base rfl,
   h2kb_stringCloneBudget_withFds_hookOk mpl mmpl hLs hMm γ tp⟩

/-- Lifts `RunHooksPlaced` from `A` to `withFds A` for an arbitrary `CliGhostHooks` bundle. -/
theorem cliRunHooksPlaced_of_ghost_withFds [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostSpqrAllocHooks M A lim gh)
    (hStrFsT : ∀ f, gh.stringClone = some f → HookFsTraced IsFsC f)
    (hStrClone : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hStrFs : ∀ fn,
      cliGhostExterns gh (cliExternsPlaced mmpl W) lsStringCloneSym = some fn →
      ∀ s0 : State, (fn s0).fs = s0.fs) :
    RunHooksPlaced (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliRunHooksPlaced_of_ghost mmpl gh W
    (cliGhostSpqrAllocHooks_withFds hG)
    hStrFsT
    (hookSat_stringCloneBudget_withFds hStrClone hStrFs)

theorem h2kb_hole2_hGSpqr_withFds
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostSpqrAllocHooks fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
        (h2k_ghFixedK mpl mmpl) :=
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun γ tp => cliGhostSpqrAllocHooks_withFds (h2kb_hole2_hGSpqr mpl mmpl hLs hMm γ tp)

theorem h2kb_hole2_hG_withFds
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostAllocHooks fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
        (h2k_ghFixedK mpl mmpl) :=
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun γ tp => cliGhostAllocHooks_withFds (h2kb_hole2_hG mpl mmpl hLs hMm γ tp)

/-- Assembles the 12-field `RunHooksPlaced` bundle at
`withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)` on `h2k_ghFixedK mpl mmpl`. -/
theorem h2kb_runHooksPlaced_withFds
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @RunHooksPlaced
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
        fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
        cliBudgetLimits
        (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro W γ tp
  exact cliRunHooksPlaced_of_ghost mmpl (h2k_ghFixedK mpl mmpl) W
    (cliGhostSpqrAllocHooks_withFds (h2kb_hole2_hGSpqr mpl mmpl hLs hMm γ tp))
    (h2kb_hole2_hFs mpl mmpl hLs hMm).stringClone_fsT
    (h2kb_stringCloneBudget_withFds_hookSat mpl mmpl hLs hMm (cliExternsPlaced mmpl W) γ tp)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
