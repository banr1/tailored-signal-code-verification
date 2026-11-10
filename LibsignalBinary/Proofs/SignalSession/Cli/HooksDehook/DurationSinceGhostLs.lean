/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux -- proof-setup: allow-public-import

/-!
# `W`-Independent Route-β′ `duration_since` Ghost Hook, Consumer N1 Bridges, & Stock-Safe `StepsVisitedIn` Replay (`HooksDehook.DurationSinceGhostLs`)

Card **R3-b** (part 2 of 2; companion to `HooksDehook.DurationSinceGhost`, mirroring
`HooksDehook.BcmpGhostK` with `LinkedCallHookG`'s `roTableGuard` and Route-β′ `WithLsRet.withLsRet`):

1. **Instruction & `.rodata.cst16` source (`timeMultiLib` blocks):**
   Verified against `VerifiedLibraries.RustStd.timeMultiLib` block `0`
   (`Timespec::sub_timespec`, `60` words = `240` B = `subTimespecByteLen`), block `1`
   (`SystemTime::duration_since`, `20` words = `80` B), and `16`-byte `.rodata.cst16` entry
   `timePlacedData0` at `mpl.ρ timeRodataCst16Sym` (STOCK-PLAN `[M]` confirmed GNU and musl
   `core`/`std` copies are byte-identical). Zero `#1344` panic-stub externs are required because
   `tv_nsec < 10^9` excludes the cold `expect_failed` tail at `sub_timespec + 236`.
2. **`W`-Independent `emptyStdProg` Ghost Hooks (`f3EmptyDurationSinceGhostHook{,Ls}`):**
   Specializes `durationSinceGhostFn` and Route-β′ `durationSinceGhostFnLs` (`withLsRet`) to
   `P_real := emptyStdProg` (`= Program.ofSvc Syscall.standard`, `rfl`-equal to `hole2_emptyProg`)
   and to the concrete `80`-word `.text.lib2` hull `durationSinceHullProg mpl` at
   `hullBase + subTimespecByteLen`, discharging all `P_real` hypotheses unconditionally across C11
   §8.1 state/VM/trace preservation and consumer `HookOk` lifts (including `WithAlloc.withAlloc`).
3. **`REV-PILOT` Note N1 Downstream Consumer `rfl` Bridges & `HookOk` Corollaries:**
   Provides `rfl` equalities and ready-to-call Route-β′ `withLsRet` `HookOk` theorems for
   `Slots.durationSince{EpochAt,Epoch,EpochAlloc,Bounded}Spec`,
   `SetUnackEpochPlacedBudget.durationSinceEpochAllocBudgetSpec`,
   `PlacedDefs.durationSinceBoundedSpec`, `PlacedDefsBudgetAux.durationSinceBoundedBudgetSpec`, and
   `SegFromPlacedBudget.TempTwins.durationSinceBoundedBudgetSpec`.
4. **Stock-Safe `h2fsgen_StepsVisitedIn` First-Stop Witnesses & `GhostExternReplaysOn` / `S`:**
   Produces `h2fsgen_StepsVisitedIn keepR P_run` witnesses, direct `P_run = P_real` guarded replays,
   stock-safe `P_run → P_real` `hLiftVis` replays (with caller-`lr`-free `Ls` variants via K3's
   `∀ lr, LsRetAddr624 lr → keepR lr = false`), and single-stub `GhostExternReplaysS` /
   `GhostExternReplaysOn` packagers.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostLs

open Arm64 Arm64.Obj ProofLib
open VerifiedLibraries.RustStd (timeMultiLib timePlacedData0 timeRodataCst16Sym)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (durationSinceExactHook)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (durationSinceEpochSpec)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits OomPreserved PoolPreserved RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved durationSinceEpochBudgetSpec)
open LibsignalBinary.Heap.Fine (hookOk_withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince (
  durationSinceEpochAtSpec durationSinceBoundedAtSpec durationSinceBoundedSpec
)
open LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceVm (
  durationSinceEpochAllocSpec durationSinceEpochAllocBudgetSpec
)
open LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceBoundedVm (
  durationSinceBoundedBudgetAtSpec durationSinceBoundedBudgetSpec
  durationSinceBoundedAllocSpec durationSinceBoundedAllocBudgetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ActiveRealPre ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (f3LinkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_single_stub ghostExternReplaysS_of_single_stub
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  linkedCallHookG_eq_of_guard linkedCallHookG_activeRealPre_of_noException
  linkedCallHookG_stepsUntil linkedCallHookG_visitedIn roTableGuard roTableGuard_stripS
  ghostExternReplaysOn_of_linkedCallHookG_roTable
  ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc hookOk_withAlloc_of_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (withExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg emptyStdProg_svc f3LinkedCallHook_const_eq_linkedCallHook)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (h2fsgen_StepsVisitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode (
  masterDurationSinceSpec specStripSInvariant_masterDurationSince specPreservesFsTrace_masterDurationSince
  masterDurationSince_pre_setPC masterDurationSince_outcome_setPC subTimespecPatchedWords durationSincePatchedWords
  durationSinceHullProg durationSinceHullProg_hasWords_subTimespec durationSinceHullProg_hasWords_durationSince
  durationSinceHullProg_externAt_none durationSinceHullProg_svc subroutine_ok_masterDurationSince_of_hasWords
  hookOk_durationSinceBounded_of_master hookOk_durationSinceBoundedAlloc_of_master
  hookOk_durationSinceBoundedBudget_of_master hookOk_durationSinceBoundedAllocBudget_of_master
  hookOk_durationSinceEpoch_of_master hookOk_durationSinceEpochAlloc_of_master
  hookOk_durationSinceEpochBudget_of_master hookOk_durationSinceEpochAllocBudget_of_master
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhost (
  subTimespecByteLen hookOk_congr withLsRet_withAlloc durationSinceGhostFn durationSinceGhostFnLs
  durationSinceHullGhostFn durationSinceHullGhostFnLs specStripSInvariant_masterDurationSinceLs
  specPreservesFsTrace_masterDurationSinceLs masterDurationSinceLs_pre_setPC masterDurationSinceLs_outcome_setPC
  subroutine_ok_masterDurationSinceLs_of_hasWords durationSinceGhostFn_master_ok durationSinceGhostFnLs_masterLs_ok
  durationSinceHullGhostFn_master_ok durationSinceHullGhostFnLs_masterLs_ok
  durationSinceGhostFnLs_lsRetAddr624_of_noException durationSinceGhostFnLs_keepLr_false_of_noException
  durationSinceGhostFnLs_of_not_lsRetAddr624 durationSinceGhostFn_of_keepLr_true durationSinceGhostFnLs_of_keepLr_true
  durationSinceGhostFn_fs durationSinceGhostFnLs_fs durationSinceGhostFn_fsT durationSinceGhostFnLs_fsT
  durationSinceGhostFn_vmPreserved durationSinceGhostFnLs_vmPreserved
  durationSinceGhostFn_oomPoolPreserved durationSinceGhostFnLs_oomPoolPreserved
  durationSinceGhostFn_oracle durationSinceGhostFnLs_oracle durationSinceGhostFn_trace durationSinceGhostFnLs_trace
  hookOk_withLsRet_durationSinceBoundedAt_of_master hookOk_withLsRet_durationSinceBounded_of_master
  hookOk_withLsRet_durationSinceBounded_keepsFs_of_master hookOk_withLsRet_durationSinceBoundedAlloc_of_master
  hookOk_withLsRet_durationSinceBoundedBudgetAt_of_master hookOk_withLsRet_durationSinceBoundedBudget_of_master
  hookOk_withLsRet_durationSinceBoundedBudget_keepsFs_of_master hookOk_withLsRet_durationSinceBoundedAllocBudget_of_master
  hookOk_withLsRet_durationSinceBounded_inImage_of_master hookOk_withLsRet_durationSinceBoundedBudget_inImage_of_master
  hookOk_withLsRet_durationSinceEpochAt_of_master hookOk_withLsRet_durationSinceEpoch_of_master
  hookOk_withLsRet_durationSinceEpoch_keepsFs_of_master hookOk_withLsRet_durationSinceEpochAlloc_of_master
  hookOk_withLsRet_durationSinceEpochBudgetAt_of_master hookOk_withLsRet_durationSinceEpochBudget_of_master
  hookOk_withLsRet_durationSinceEpochBudget_keepsFs_of_master hookOk_withLsRet_durationSinceEpochAllocBudget_of_master
  hookOk_withLsRet_durationSinceEpoch_inImage_of_master hookOk_withLsRet_durationSinceEpochBudget_inImage_of_master
  durationSinceGhostFn_any_keepsFs_ok durationSinceGhostFnLs_any_keepsFs_ok
  durationSinceGhostFn_any_withOomPoolPreserved_ok durationSinceGhostFnLs_any_withOomPoolPreserved_ok
  durationSinceGhostFn_any_execFrozen_ok durationSinceGhostFnLs_any_execFrozen_ok
)

/-! ## 1. `W`-Independent `emptyStdProg` Ghost Hooks, `f3LinkedCallHook` Bridges, & `withAlloc` -/

/-- Plain `W`-independent `SystemTime::duration_since` ghost hook (`P_real := emptyStdProg`). -/
@[expose] noncomputable def f3EmptyDurationSinceGhostHook
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_sub : Program)
    (entry : BitVec 64) : State → State :=
  durationSinceGhostFn cst16Addr keepR emptyStdProg P_sub entry

/-- Route-β′ (`withLsRet masterDurationSinceSpec`) `W`-independent `duration_since` ghost hook. -/
@[expose] noncomputable def f3EmptyDurationSinceGhostHookLs [LibsignalPlacement]
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_sub : Program)
    (entry : BitVec 64) : State → State :=
  durationSinceGhostFnLs cst16Addr keepR emptyStdProg P_sub entry

/-- Concrete `80`-word `.text.lib2` hull specialization of `f3EmptyDurationSinceGhostHook`. -/
noncomputable abbrev f3EmptyDurationSinceHullGhostHook
    (keepR : BitVec 64 → Bool) (mpl : MultiPlacement) (hullBase : BitVec 64) : State → State :=
  f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR
    (durationSinceHullProg mpl) (hullBase + subTimespecByteLen)

/-- Concrete `80`-word `.text.lib2` hull specialization of `f3EmptyDurationSinceGhostHookLs`. -/
noncomputable abbrev f3EmptyDurationSinceHullGhostHookLs [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (mpl : MultiPlacement) (hullBase : BitVec 64) : State → State :=
  f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR
    (durationSinceHullProg mpl) (hullBase + subTimespecByteLen)

theorem f3EmptyDurationSinceGhostHook_eq
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_sub : Program) (entry : BitVec 64) :
    f3EmptyDurationSinceGhostHook cst16Addr keepR P_sub entry =
      durationSinceGhostFn cst16Addr keepR emptyStdProg P_sub entry := rfl

theorem f3EmptyDurationSinceGhostHookLs_eq [LibsignalPlacement]
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_sub : Program) (entry : BitVec 64) :
    f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry =
      durationSinceGhostFnLs cst16Addr keepR emptyStdProg P_sub entry := rfl

theorem f3EmptyDurationSinceGhostHook_eq_f3LinkedCallHook_of_guard
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_sub : Program} {entry : BitVec 64}
    {s0 : State} (hG : roTableGuard cst16Addr timePlacedData0 s0) :
    f3EmptyDurationSinceGhostHook cst16Addr keepR P_sub entry s0 =
      f3LinkedCallHook keepR emptyStdProg P_sub entry
        (fun _ _ => masterDurationSinceSpec) durationSinceExactHook s0 := by
  unfold f3EmptyDurationSinceGhostHook durationSinceGhostFn
  rw [linkedCallHookG_eq_of_guard hG,
    ← f3LinkedCallHook_const_eq_linkedCallHook keepR emptyStdProg P_sub entry
      masterDurationSinceSpec durationSinceExactHook]

theorem f3EmptyDurationSinceGhostHookLs_eq_f3LinkedCallHook_of_guard [LibsignalPlacement]
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_sub : Program} {entry : BitVec 64}
    {s0 : State} (hG : roTableGuard cst16Addr timePlacedData0 s0) :
    f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry s0 =
      f3LinkedCallHook keepR emptyStdProg P_sub entry
        (fun _ _ => withLsRet masterDurationSinceSpec) durationSinceExactHook s0 := by
  unfold f3EmptyDurationSinceGhostHookLs durationSinceGhostFnLs
  rw [linkedCallHookG_eq_of_guard hG,
    ← f3LinkedCallHook_const_eq_linkedCallHook keepR emptyStdProg P_sub entry
      (withLsRet masterDurationSinceSpec) durationSinceExactHook]

theorem hookOk_withAlloc_of_hookOk_and_vm {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {f : State → State} {spec : Spec α}
    (hh : HookOk f spec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withAlloc (M := M) A lim spec) :=
  hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved hh hvm)

theorem hookOk_withLsRet_withAlloc_of_hookOk_and_vm [LibsignalPlacement] {α : Type}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {f : State → State} {spec : Spec α}
    (hh : HookOk f (withLsRet spec)) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet (withAlloc (M := M) A lim spec)) := by
  rw [withLsRet_withAlloc]
  exact hookOk_withAlloc_of_hookOk_and_vm A lim hh hvm

/-! ## 2. C11 §8.1 State / VM / Trace / `lr` Properties (`P_real` Hypotheses Discharged) -/

theorem f3EmptyDurationSinceGhostHook_fs
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_sub : Program)
    (entry : BitVec 64) (s0 : State) :
    (f3EmptyDurationSinceGhostHook cst16Addr keepR P_sub entry s0).fs = s0.fs :=
  durationSinceGhostFn_fs cst16Addr keepR emptyStdProg P_sub entry s0

theorem f3EmptyDurationSinceGhostHookLs_fs [LibsignalPlacement]
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_sub : Program)
    (entry : BitVec 64) (s0 : State) :
    (f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry s0).fs = s0.fs :=
  durationSinceGhostFnLs_fs cst16Addr keepR emptyStdProg P_sub entry s0

theorem f3EmptyDurationSinceGhostHook_fsT
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_sub : Program) (entry : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyDurationSinceGhostHook cst16Addr keepR P_sub entry) :=
  durationSinceGhostFn_fsT cst16Addr keepR emptyStdProg P_sub entry

theorem f3EmptyDurationSinceGhostHookLs_fsT [LibsignalPlacement]
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_sub : Program) (entry : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry) :=
  durationSinceGhostFnLs_fsT cst16Addr keepR emptyStdProg P_sub entry

section StateProps

variable {keepR : BitVec 64 → Bool} {P_sub : Program} {mpl : MultiPlacement}
  (hpl : timeMultiLib.Placeable mpl) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
  (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
include hpl hsvc_sub hsub_no hw0 hw1

theorem f3EmptyDurationSinceGhostHook_vmPreserved (s0 : State) :
    VmPreserved s0
      (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) s0) :=
  durationSinceGhostFn_vmPreserved hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1 s0

theorem f3EmptyDurationSinceGhostHookLs_vmPreserved [LibsignalPlacement] (s0 : State) :
    VmPreserved s0
      (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) s0) :=
  durationSinceGhostFnLs_vmPreserved hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1 s0

theorem f3EmptyDurationSinceGhostHook_oomPoolPreserved (s0 : State) :
    OomPreserved s0
        (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) s0) ∧
      PoolPreserved s0
        (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) s0) :=
  durationSinceGhostFn_oomPoolPreserved hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1 s0

theorem f3EmptyDurationSinceGhostHookLs_oomPoolPreserved [LibsignalPlacement] (s0 : State) :
    OomPreserved s0
        (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) s0) ∧
      PoolPreserved s0
        (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) s0) :=
  durationSinceGhostFnLs_oomPoolPreserved hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1 s0

theorem f3EmptyDurationSinceGhostHook_oracle (s0 : State) :
    (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) s0).oracle =
      s0.oracle :=
  durationSinceGhostFn_oracle hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1 s0

theorem f3EmptyDurationSinceGhostHookLs_oracle [LibsignalPlacement] (s0 : State) :
    (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub
        (mpl.base 1) s0).oracle = s0.oracle :=
  durationSinceGhostFnLs_oracle hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1 s0

theorem f3EmptyDurationSinceGhostHook_trace (s0 : State) :
    (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) s0).trace =
      s0.trace :=
  durationSinceGhostFn_trace hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1 s0

theorem f3EmptyDurationSinceGhostHookLs_trace [LibsignalPlacement] (s0 : State) :
    (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub
        (mpl.base 1) s0).trace = s0.trace :=
  durationSinceGhostFnLs_trace hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1 s0

end StateProps

theorem f3EmptyDurationSinceHullGhostHook_vmPreserved
    {keepR : BitVec 64 → Bool} {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl) (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen) (s0 : State) :
    VmPreserved s0 (f3EmptyDurationSinceHullGhostHook keepR mpl hullBase s0) := by
  unfold f3EmptyDurationSinceHullGhostHook; rw [← hb1]
  refine f3EmptyDurationSinceGhostHook_vmPreserved hpl (durationSinceHullProg_svc mpl)
    (durationSinceHullProg_externAt_none mpl) (durationSinceHullProg_hasWords_subTimespec mpl) ?_ s0
  rw [hb1, ← hb0]; exact durationSinceHullProg_hasWords_durationSince mpl

theorem f3EmptyDurationSinceHullGhostHookLs_vmPreserved [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl) (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen) (s0 : State) :
    VmPreserved s0 (f3EmptyDurationSinceHullGhostHookLs keepR mpl hullBase s0) := by
  unfold f3EmptyDurationSinceHullGhostHookLs; rw [← hb1]
  refine f3EmptyDurationSinceGhostHookLs_vmPreserved hpl (durationSinceHullProg_svc mpl)
    (durationSinceHullProg_externAt_none mpl) (durationSinceHullProg_hasWords_subTimespec mpl) ?_ s0
  rw [hb1, ← hb0]; exact durationSinceHullProg_hasWords_durationSince mpl

theorem f3EmptyDurationSinceHullGhostHookLs_oomPoolPreserved [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl) (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen) (s0 : State) :
    OomPreserved s0 (f3EmptyDurationSinceHullGhostHookLs keepR mpl hullBase s0) ∧
      PoolPreserved s0 (f3EmptyDurationSinceHullGhostHookLs keepR mpl hullBase s0) := by
  unfold f3EmptyDurationSinceHullGhostHookLs; rw [← hb1]
  refine f3EmptyDurationSinceGhostHookLs_oomPoolPreserved hpl (durationSinceHullProg_svc mpl)
    (durationSinceHullProg_externAt_none mpl) (durationSinceHullProg_hasWords_subTimespec mpl) ?_ s0
  rw [hb1, ← hb0]; exact durationSinceHullProg_hasWords_durationSince mpl

theorem f3EmptyDurationSinceHullGhostHookLs_oracle [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl) (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen) (s0 : State) :
    (f3EmptyDurationSinceHullGhostHookLs keepR mpl hullBase s0).oracle = s0.oracle := by
  unfold f3EmptyDurationSinceHullGhostHookLs; rw [← hb1]
  refine f3EmptyDurationSinceGhostHookLs_oracle hpl (durationSinceHullProg_svc mpl)
    (durationSinceHullProg_externAt_none mpl) (durationSinceHullProg_hasWords_subTimespec mpl) ?_ s0
  rw [hb1, ← hb0]; exact durationSinceHullProg_hasWords_durationSince mpl

theorem f3EmptyDurationSinceHullGhostHookLs_trace [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl) (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen) (s0 : State) :
    (f3EmptyDurationSinceHullGhostHookLs keepR mpl hullBase s0).trace = s0.trace := by
  unfold f3EmptyDurationSinceHullGhostHookLs; rw [← hb1]
  refine f3EmptyDurationSinceGhostHookLs_trace hpl (durationSinceHullProg_svc mpl)
    (durationSinceHullProg_externAt_none mpl) (durationSinceHullProg_hasWords_subTimespec mpl) ?_ s0
  rw [hb1, ← hb0]; exact durationSinceHullProg_hasWords_durationSince mpl

theorem f3EmptyDurationSinceGhostHookLs_lsRetAddr624_of_noException [LibsignalPlacement]
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_sub : Program}
    {entry : BitVec 64} {u : State}
    (hnoex : ∀ msg,
      (f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) :=
  durationSinceGhostFnLs_lsRetAddr624_of_noException hnoex

theorem f3EmptyDurationSinceGhostHookLs_keepLr_false_of_noException [LibsignalPlacement]
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_sub : Program}
    {entry : BitVec 64} {u : State}
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hnoex : ∀ msg,
      (f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry u).status ≠ .Exception msg) :
    keepR (u.readReg64 .lr) = false :=
  durationSinceGhostFnLs_keepLr_false_of_noException hKeep hnoex

theorem f3EmptyDurationSinceGhostHookLs_of_not_lsRetAddr624 [LibsignalPlacement]
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_sub : Program}
    {entry : BitVec 64} {s0 : State} (hnLr : ¬ LsRetAddr624 (s0.readReg64 .lr)) :
    f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } :=
  durationSinceGhostFnLs_of_not_lsRetAddr624 hnLr

open Classical in
theorem f3EmptyDurationSinceGhostHook_of_keepLr_true
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_sub : Program}
    {entry : BitVec 64} {s0 : State} (hlr : keepR (s0.readReg64 .lr) = true) :
    f3EmptyDurationSinceGhostHook cst16Addr keepR P_sub entry s0 =
      if _ : ActiveRealPre masterDurationSinceSpec s0 then durationSinceExactHook s0
      else { s0 with status := .Exception "ghost-hook precondition violated" } :=
  durationSinceGhostFn_of_keepLr_true hlr

open Classical in
theorem f3EmptyDurationSinceGhostHookLs_of_keepLr_true [LibsignalPlacement]
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_sub : Program}
    {entry : BitVec 64} {s0 : State} (hlr : keepR (s0.readReg64 .lr) = true) :
    f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry s0 =
      if _ : ActiveRealPre (withLsRet masterDurationSinceSpec) s0 then durationSinceExactHook s0
      else { s0 with status := .Exception "ghost-hook precondition violated" } :=
  durationSinceGhostFnLs_of_keepLr_true hlr

/-! ## 3. Consumer `HookOk` Suite on `f3EmptyDurationSinceGhostHook{,Ls}` & Hull -/

section HookOkForwarding

variable {keepR : BitVec 64 → Bool} {P_sub : Program} {mpl : MultiPlacement}
  (hpl : timeMultiLib.Placeable mpl) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
  (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
include hpl hsvc_sub hsub_no hw0 hw1

theorem f3EmptyDurationSinceGhostHook_master_ok :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      masterDurationSinceSpec :=
  durationSinceGhostFn_master_ok hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1

theorem f3EmptyDurationSinceGhostHookLs_masterLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet masterDurationSinceSpec) :=
  durationSinceGhostFnLs_masterLs_ok hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1

theorem f3EmptyDurationSinceGhostHook_bounded_ok :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      durationSinceBoundedSpec :=
  hookOk_durationSinceBounded_of_master (f3EmptyDurationSinceGhostHook_master_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHook_boundedAlloc_ok :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      durationSinceBoundedAllocSpec :=
  hookOk_durationSinceBoundedAlloc_of_master (f3EmptyDurationSinceGhostHook_master_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHook_boundedBudget_ok :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      durationSinceBoundedBudgetSpec :=
  hookOk_durationSinceBoundedBudget_of_master
    (f3EmptyDurationSinceGhostHook_master_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHook_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHook_boundedAllocBudget_ok :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      durationSinceBoundedAllocBudgetSpec :=
  hookOk_durationSinceBoundedAllocBudget_of_master
    (f3EmptyDurationSinceGhostHook_master_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHook_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHook_epoch_ok :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      durationSinceEpochSpec :=
  hookOk_durationSinceEpoch_of_master (f3EmptyDurationSinceGhostHook_master_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHook_epochAlloc_ok :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      durationSinceEpochAllocSpec :=
  hookOk_durationSinceEpochAlloc_of_master (f3EmptyDurationSinceGhostHook_master_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHook_epochBudget_ok :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      durationSinceEpochBudgetSpec :=
  hookOk_durationSinceEpochBudget_of_master
    (f3EmptyDurationSinceGhostHook_master_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHook_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHook_epochAllocBudget_ok :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      durationSinceEpochAllocBudgetSpec :=
  hookOk_durationSinceEpochAllocBudget_of_master
    (f3EmptyDurationSinceGhostHook_master_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHook_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

/-- Route-β′ (`withLsRet`) consumer `HookOk` arms on `f3EmptyDurationSinceGhostHookLs`. -/
theorem f3EmptyDurationSinceGhostHookLs_boundedAtLs_ok [LibsignalPlacement]
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet (durationSinceBoundedAtSpec stk)) :=
  hookOk_withLsRet_durationSinceBoundedAt_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1) hstk

theorem f3EmptyDurationSinceGhostHookLs_boundedLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceBoundedSpec) :=
  hookOk_withLsRet_durationSinceBounded_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_bounded_keepsFsLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceBoundedSpec.keepsFs) :=
  hookOk_withLsRet_durationSinceBounded_keepsFs_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_boundedAllocLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceBoundedAllocSpec) :=
  hookOk_withLsRet_durationSinceBoundedAlloc_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_boundedBudgetAtLs_ok [LibsignalPlacement]
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet (durationSinceBoundedBudgetAtSpec stk)) :=
  hookOk_withLsRet_durationSinceBoundedBudgetAt_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1) hstk

theorem f3EmptyDurationSinceGhostHookLs_boundedBudgetLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceBoundedBudgetSpec) :=
  hookOk_withLsRet_durationSinceBoundedBudget_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_boundedBudget_keepsFsLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceBoundedBudgetSpec.keepsFs) :=
  hookOk_withLsRet_durationSinceBoundedBudget_keepsFs_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_boundedAllocBudgetLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceBoundedAllocBudgetSpec) :=
  hookOk_withLsRet_durationSinceBoundedAllocBudget_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_bounded_inImageLs_ok [LibsignalPlacement] (img : Image) :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet (durationSinceBoundedSpec.inImage img)) :=
  hookOk_withLsRet_durationSinceBounded_inImage_of_master img
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_boundedBudget_inImageLs_ok [LibsignalPlacement] (img : Image) :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet (durationSinceBoundedBudgetSpec.inImage img)) :=
  hookOk_withLsRet_durationSinceBoundedBudget_inImage_of_master img
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_epochAtLs_ok [LibsignalPlacement]
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet (durationSinceEpochAtSpec stk)) :=
  hookOk_withLsRet_durationSinceEpochAt_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1) hstk

theorem f3EmptyDurationSinceGhostHookLs_epochLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceEpochSpec) :=
  hookOk_withLsRet_durationSinceEpoch_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_epoch_keepsFsLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceEpochSpec.keepsFs) :=
  hookOk_withLsRet_durationSinceEpoch_keepsFs_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_epochAllocLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceEpochAllocSpec) :=
  hookOk_withLsRet_durationSinceEpochAlloc_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_epochBudgetAtLs_ok [LibsignalPlacement]
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet (withVmPreserved (durationSinceEpochAtSpec stk))) :=
  hookOk_withLsRet_durationSinceEpochBudgetAt_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1) hstk

theorem f3EmptyDurationSinceGhostHookLs_epochBudgetLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceEpochBudgetSpec) :=
  hookOk_withLsRet_durationSinceEpochBudget_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_epochBudget_keepsFsLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceEpochBudgetSpec.keepsFs) :=
  hookOk_withLsRet_durationSinceEpochBudget_keepsFs_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_epochAllocBudgetLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet durationSinceEpochAllocBudgetSpec) :=
  hookOk_withLsRet_durationSinceEpochAllocBudget_of_master
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_epoch_inImageLs_ok [LibsignalPlacement] (img : Image) :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet (durationSinceEpochSpec.inImage img)) :=
  hookOk_withLsRet_durationSinceEpoch_inImage_of_master img
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_epochBudget_inImageLs_ok [LibsignalPlacement] (img : Image) :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet (durationSinceEpochBudgetSpec.inImage img)) :=
  hookOk_withLsRet_durationSinceEpochBudget_inImage_of_master img
    (f3EmptyDurationSinceGhostHookLs_masterLs_ok hpl hsvc_sub hsub_no hw0 hw1)
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHook_any_withAlloc_ok {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {spec : Spec α}
    (hh : HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1)) spec) :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withAlloc (M := M) A lim spec) :=
  hookOk_withAlloc_of_hookOk_and_vm A lim hh
    (f3EmptyDurationSinceGhostHook_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHookLs_any_withAlloc_ok [LibsignalPlacement] {α : Type}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {spec : Spec α}
    (hh : HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub
      (mpl.base 1)) (withLsRet spec)) :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet (withAlloc (M := M) A lim spec)) :=
  hookOk_withLsRet_withAlloc_of_hookOk_and_vm A lim hh
    (f3EmptyDurationSinceGhostHookLs_vmPreserved hpl hsvc_sub hsub_no hw0 hw1)

theorem f3EmptyDurationSinceGhostHook_any_withOomPoolPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1)) spec) :
    HookOk (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withOomPoolPreserved spec) :=
  durationSinceGhostFn_any_withOomPoolPreserved_ok hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl)
    hsub_no hw0 hw1 hh

theorem f3EmptyDurationSinceGhostHookLs_any_withOomPoolPreserved_ok [LibsignalPlacement] {α : Type}
    {spec : Spec α}
    (hh : HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub
      (mpl.base 1)) (withLsRet spec)) :
    HookOk (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1))
      (withLsRet (withOomPoolPreserved spec)) :=
  durationSinceGhostFnLs_any_withOomPoolPreserved_ok hpl emptyStdProg_svc hsvc_sub
    (fun _ _ => rfl) hsub_no hw0 hw1 hh

omit hpl hsvc_sub hsub_no hw0 hw1

theorem f3EmptyDurationSinceGhostHook_any_keepsFs_ok {α : Type}
    {cst16Addr entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (f3EmptyDurationSinceGhostHook cst16Addr keepR P_sub entry) spec) :
    HookOk (f3EmptyDurationSinceGhostHook cst16Addr keepR P_sub entry) spec.keepsFs :=
  durationSinceGhostFn_any_keepsFs_ok hh

theorem f3EmptyDurationSinceGhostHookLs_any_keepsFs_ok [LibsignalPlacement] {α : Type}
    {cst16Addr entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry) (withLsRet spec)) :
    HookOk (f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry) (withLsRet spec.keepsFs) :=
  durationSinceGhostFnLs_any_keepsFs_ok hh

theorem f3EmptyDurationSinceGhostHook_any_execFrozen_ok {α : Type}
    {cst16Addr entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (f3EmptyDurationSinceGhostHook cst16Addr keepR P_sub entry) spec) :
    HookOk (f3EmptyDurationSinceGhostHook cst16Addr keepR P_sub entry) (withExecFrozen spec) :=
  durationSinceGhostFn_any_execFrozen_ok hh

theorem f3EmptyDurationSinceGhostHookLs_any_execFrozen_ok [LibsignalPlacement] {α : Type}
    {cst16Addr entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry) (withLsRet spec)) :
    HookOk (f3EmptyDurationSinceGhostHookLs cst16Addr keepR P_sub entry)
      (withLsRet (withExecFrozen spec)) :=
  durationSinceGhostFnLs_any_execFrozen_ok hh

end HookOkForwarding

theorem f3EmptyDurationSinceHullGhostHook_master_ok
    {keepR : BitVec 64 → Bool} {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl) (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen) :
    HookOk (f3EmptyDurationSinceHullGhostHook keepR mpl hullBase) masterDurationSinceSpec :=
  durationSinceHullGhostFn_master_ok hullBase hpl hb0 hb1 emptyStdProg_svc (fun _ _ => rfl)

theorem f3EmptyDurationSinceHullGhostHookLs_masterLs_ok [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl) (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen) :
    HookOk (f3EmptyDurationSinceHullGhostHookLs keepR mpl hullBase)
      (withLsRet masterDurationSinceSpec) :=
  durationSinceHullGhostFnLs_masterLs_ok hullBase hpl hb0 hb1 emptyStdProg_svc (fun _ _ => rfl)

/-! ## 4. `REV-PILOT` Note N1 `rfl` Bridges & Downstream Consumer `HookOk` Corollaries -/

theorem slots_durationSinceEpochAtSpec_eq (stk : Nat) :
    CryptoVerification.SignalSession.Cli.Slots.durationSinceEpochAtSpec stk =
      durationSinceEpochAtSpec stk := rfl

theorem slots_durationSinceEpochSpec_eq :
    CryptoVerification.SignalSession.Cli.Slots.durationSinceEpochSpec =
      durationSinceEpochSpec := rfl

theorem slots_durationSinceEpochAllocSpec_eq :
    CryptoVerification.SignalSession.Cli.Slots.durationSinceEpochAllocSpec =
      durationSinceEpochAllocSpec := rfl

theorem slots_durationSinceBoundedSpec_eq :
    CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec =
      durationSinceBoundedSpec := rfl

theorem setUnack_durationSinceEpochAllocBudgetSpec_eq :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget.durationSinceEpochAllocBudgetSpec =
      durationSinceEpochAllocBudgetSpec := rfl

theorem placedDefs_durationSinceBoundedSpec_eq :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.durationSinceBoundedSpec =
      durationSinceBoundedSpec := rfl

theorem placedDefsBudgetAux_durationSinceBoundedBudgetSpec_eq :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.durationSinceBoundedBudgetSpec =
      durationSinceBoundedBudgetSpec := rfl

theorem segFromTempTwins_durationSinceBoundedBudgetSpec_eq :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.durationSinceBoundedBudgetSpec =
      durationSinceBoundedBudgetSpec := rfl

theorem hookOk_withLsRet_slots_durationSinceEpochAt_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (CryptoVerification.SignalSession.Cli.Slots.durationSinceEpochAtSpec stk)) :=
  hookOk_congr (congrArg withLsRet (slots_durationSinceEpochAtSpec_eq stk).symm)
    (hookOk_withLsRet_durationSinceEpochAt_of_master hh hstk)

theorem hookOk_withLsRet_slots_durationSinceEpoch_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet CryptoVerification.SignalSession.Cli.Slots.durationSinceEpochSpec) :=
  hookOk_congr (congrArg withLsRet slots_durationSinceEpochSpec_eq.symm)
    (hookOk_withLsRet_durationSinceEpoch_of_master hh)

theorem hookOk_withLsRet_slots_durationSinceEpochAlloc_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet CryptoVerification.SignalSession.Cli.Slots.durationSinceEpochAllocSpec) :=
  hookOk_congr (congrArg withLsRet slots_durationSinceEpochAllocSpec_eq.symm)
    (hookOk_withLsRet_durationSinceEpochAlloc_of_master hh)

theorem hookOk_withLsRet_slots_durationSinceBounded_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec) :=
  hookOk_congr (congrArg withLsRet slots_durationSinceBoundedSpec_eq.symm)
    (hookOk_withLsRet_durationSinceBounded_of_master hh)

theorem hookOk_withLsRet_setUnack_durationSinceEpochAllocBudget_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget.durationSinceEpochAllocBudgetSpec) :=
  hookOk_congr (congrArg withLsRet setUnack_durationSinceEpochAllocBudgetSpec_eq.symm)
    (hookOk_withLsRet_durationSinceEpochAllocBudget_of_master hh hvm)

theorem hookOk_withLsRet_placedDefs_durationSinceBounded_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.durationSinceBoundedSpec) :=
  hookOk_congr (congrArg withLsRet placedDefs_durationSinceBoundedSpec_eq.symm)
    (hookOk_withLsRet_durationSinceBounded_of_master hh)

theorem hookOk_withLsRet_placedDefsBudgetAux_durationSinceBoundedBudget_of_master
    [LibsignalPlacement] {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet
      LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.durationSinceBoundedBudgetSpec) :=
  hookOk_congr (congrArg withLsRet placedDefsBudgetAux_durationSinceBoundedBudgetSpec_eq.symm)
    (hookOk_withLsRet_durationSinceBoundedBudget_of_master hh hvm)

theorem hookOk_withLsRet_segFromTempTwins_durationSinceBoundedBudget_of_master
    [LibsignalPlacement] {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet
      LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.durationSinceBoundedBudgetSpec) :=
  hookOk_congr (congrArg withLsRet segFromTempTwins_durationSinceBoundedBudgetSpec_eq.symm)
    (hookOk_withLsRet_durationSinceBoundedBudget_of_master hh hvm)

/-! ## 5. Stock-Safe `h2fsgen_StepsVisitedIn` First-Stop Witnesses & `GhostExternReplaysOn` / `S` -/

theorem durationSinceGhostFn_visitedIn
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    {u : State} (hRo : RoDataAt u.mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hnoex : ∀ msg,
      (durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub
        (mpl.base 1) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keepR (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    let sf := durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub (mpl.base 1) u
    StepsUntil P_run (SubroutineStop u) (u.setPC (mpl.base 1)) sf ∧
      SubroutineStop u sf ∧ ExecFrozen sf.mem ∧ sf.fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (mpl.base 1)) sf := by
  have hActPre : ActiveRealPre masterDurationSinceSpec u :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  have hOk := subroutine_ok_masterDurationSince_of_hasWords hpl hsvc_sub hsub_no hw0 hw1
  have hGS := roTableGuard_stripS keepR (mpl.base 1) (mpl.ρ timeRodataCst16Sym) timePlacedData0
  obtain ⟨huntil, hstop, hfr_sf⟩ :=
    linkedCallHookG_stepsUntil (fallback := durationSinceExactHook)
      hsvc_run hsvc_sub hrun_no hsub_no hGS hOk
      (specStripSInvariant_masterDurationSince keepR) specPreservesFsTrace_masterDurationSince
      masterDurationSince_pre_setPC masterDurationSince_outcome_setPC
      hRo hActPre hFr hlr_out hCodeSub
  obtain ⟨hvis, _⟩ :=
    linkedCallHookG_visitedIn (fallback := durationSinceExactHook)
      hsvc_run hsvc_sub hrun_no hsub_no hGS hOk
      (specStripSInvariant_masterDurationSince keepR) specPreservesFsTrace_masterDurationSince
      masterDurationSince_pre_setPC masterDurationSince_outcome_setPC
      hRo hActPre hFr hlr_out hCodeSub
  exact ⟨huntil, hstop, hfr_sf,
    durationSinceGhostFn_fs (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub (mpl.base 1) u, hvis⟩

theorem durationSinceGhostFnLs_visitedIn [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    {u : State} (hRo : RoDataAt u.mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hnoex : ∀ msg,
      (durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub
        (mpl.base 1) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    let sf := durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub (mpl.base 1) u
    StepsUntil P_run (SubroutineStop u) (u.setPC (mpl.base 1)) sf ∧
      SubroutineStop u sf ∧ ExecFrozen sf.mem ∧ sf.fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (mpl.base 1)) sf := by
  have hlr_out := durationSinceGhostFnLs_keepLr_false_of_noException hKeep hnoex
  have hActPre : ActiveRealPre (withLsRet masterDurationSinceSpec) u :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  have hOk := subroutine_ok_masterDurationSinceLs_of_hasWords hpl hsvc_sub hsub_no hw0 hw1
  have hGS := roTableGuard_stripS keepR (mpl.base 1) (mpl.ρ timeRodataCst16Sym) timePlacedData0
  obtain ⟨huntil, hstop, hfr_sf⟩ :=
    linkedCallHookG_stepsUntil (fallback := durationSinceExactHook)
      hsvc_run hsvc_sub hrun_no hsub_no hGS hOk
      (specStripSInvariant_masterDurationSinceLs keepR) specPreservesFsTrace_masterDurationSinceLs
      masterDurationSinceLs_pre_setPC masterDurationSinceLs_outcome_setPC
      hRo hActPre hFr hlr_out hCodeSub
  obtain ⟨hvis, _⟩ :=
    linkedCallHookG_visitedIn (fallback := durationSinceExactHook)
      hsvc_run hsvc_sub hrun_no hsub_no hGS hOk
      (specStripSInvariant_masterDurationSinceLs keepR) specPreservesFsTrace_masterDurationSinceLs
      masterDurationSinceLs_pre_setPC masterDurationSinceLs_outcome_setPC
      hRo hActPre hFr hlr_out hCodeSub
  exact ⟨huntil, hstop, hfr_sf,
    durationSinceGhostFnLs_fs (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub (mpl.base 1) u, hvis⟩

theorem f3EmptyDurationSinceGhostHook_visitedIn
    {keepR : BitVec 64 → Bool} {P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    {u : State} (hRo : RoDataAt u.mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hnoex : ∀ msg,
      (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub
        (mpl.base 1) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keepR (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    let sf := f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) u
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC (mpl.base 1)) sf ∧
      SubroutineStop u sf ∧ ExecFrozen sf.mem ∧ sf.fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (mpl.base 1)) sf :=
  durationSinceGhostFn_visitedIn hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1
    hRo hnoex hFr hlr_out hCodeSub

theorem f3EmptyDurationSinceGhostHookLs_visitedIn [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    {u : State} (hRo : RoDataAt u.mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hnoex : ∀ msg,
      (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub
        (mpl.base 1) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    let sf := f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) u
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC (mpl.base 1)) sf ∧
      SubroutineStop u sf ∧ ExecFrozen sf.mem ∧ sf.fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (mpl.base 1)) sf :=
  durationSinceGhostFnLs_visitedIn hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1
    hKeep hRo hnoex hFr hCodeSub

theorem durationSinceGhostFn_replaysOn
    {InvMem : Memory → Prop} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {mpl : MultiPlacement} {stubPc : BitVec 64}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mpl.base 1))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hRoInv : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      RoDataAt mem (mpl.ρ timeRodataCst16Sym) timePlacedData0) :
    let f := durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1)
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      ExecFrozen u.mem → keepR (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvMem (f u).mem ∧ (f u).fs = u.fs := by
  have hRep :=
    ghostExternReplaysOn_of_linkedCallHookG_roTable (fallback := durationSinceExactHook)
      hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf hRoInv
      (subroutine_ok_masterDurationSince_of_hasWords hpl hsvc_sub hsub_no hw0 hw1)
      (specStripSInvariant_masterDurationSince keepR) specPreservesFsTrace_masterDurationSince
      masterDurationSince_pre_setPC masterDurationSince_outcome_setPC
  refine ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨hs, hfr', hinv'⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
  exact ⟨hs, hfr', hinv',
    durationSinceGhostFn_fs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) u⟩

theorem durationSinceGhostFnLs_replaysOn_of_lrKeep [LibsignalPlacement]
    {InvMem : Memory → Prop} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {mpl : MultiPlacement} {stubPc : BitVec 64}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mpl.base 1))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hRoInv : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      RoDataAt mem (mpl.ρ timeRodataCst16Sym) timePlacedData0) :
    let f := durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1)
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvMem (f u).mem ∧ (f u).fs = u.fs := by
  have hRep :=
    ghostExternReplaysOn_of_linkedCallHookG_roTable (fallback := durationSinceExactHook)
      hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf hRoInv
      (subroutine_ok_masterDurationSinceLs_of_hasWords hpl hsvc_sub hsub_no hw0 hw1)
      (specStripSInvariant_masterDurationSinceLs keepR) specPreservesFsTrace_masterDurationSinceLs
      masterDurationSinceLs_pre_setPC masterDurationSinceLs_outcome_setPC
  refine ⟨hRep.1, fun u hpc hrun hnoex hfr hinv => ?_⟩
  have hlr := durationSinceGhostFnLs_keepLr_false_of_noException hKeep hnoex
  obtain ⟨hs, hfr', hinv'⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
  exact ⟨hs, hfr', hinv',
    durationSinceGhostFnLs_fs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) u⟩

theorem durationSinceGhostFn_replayOn_of_visitedIn
    {InvMem : Memory → Prop} {keepR : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {mpl : MultiPlacement} {stubPc : BitVec 64}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mpl.base 1))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hRoInv : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      RoDataAt mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (mpl.base 1)) sf →
      Steps P_real (u.setPC (mpl.base 1)) sf) :
    let f := durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub (mpl.base 1)
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      ExecFrozen u.mem → keepR (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvMem (f u).mem ∧ (f u).fs = u.fs := by
  have hRep :=
    ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis (fallback := durationSinceExactHook)
      hsvc_run hsvc_sub hrun_no hsub_no hreal_stub_none hStub hLiftVis hInvLoaded hInvKf hRoInv
      (subroutine_ok_masterDurationSince_of_hasWords hpl hsvc_sub hsub_no hw0 hw1)
      (specStripSInvariant_masterDurationSince keepR) specPreservesFsTrace_masterDurationSince
      masterDurationSince_pre_setPC masterDurationSince_outcome_setPC
  refine ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨hs, hfr', hinv'⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
  exact ⟨hs, hfr', hinv',
    durationSinceGhostFn_fs (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub (mpl.base 1) u⟩

theorem durationSinceGhostFnLs_replayOn_of_visitedIn_of_lrKeep [LibsignalPlacement]
    {InvMem : Memory → Prop} {keepR : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {mpl : MultiPlacement} {stubPc : BitVec 64}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mpl.base 1))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hRoInv : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      RoDataAt mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (mpl.base 1)) sf →
      Steps P_real (u.setPC (mpl.base 1)) sf) :
    let f := durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub (mpl.base 1)
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvMem (f u).mem ∧ (f u).fs = u.fs := by
  have hRep :=
    ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis (fallback := durationSinceExactHook)
      hsvc_run hsvc_sub hrun_no hsub_no hreal_stub_none hStub hLiftVis hInvLoaded hInvKf hRoInv
      (subroutine_ok_masterDurationSinceLs_of_hasWords hpl hsvc_sub hsub_no hw0 hw1)
      (specStripSInvariant_masterDurationSinceLs keepR) specPreservesFsTrace_masterDurationSinceLs
      masterDurationSinceLs_pre_setPC masterDurationSinceLs_outcome_setPC
  refine ⟨hRep.1, fun u hpc hrun hnoex hfr hinv => ?_⟩
  have hlr := durationSinceGhostFnLs_keepLr_false_of_noException hKeep hnoex
  obtain ⟨hs, hfr', hinv'⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
  exact ⟨hs, hfr', hinv',
    durationSinceGhostFnLs_fs (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub (mpl.base 1) u⟩

theorem f3EmptyDurationSinceGhostHook_replayOn_of_visitedIn
    {InvMem : Memory → Prop} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {mpl : MultiPlacement} {stubPc : BitVec 64}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mpl.base 1))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hRoInv : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      RoDataAt mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (mpl.base 1)) sf →
      Steps P_real (u.setPC (mpl.base 1)) sf) :
    let f := f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1)
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      ExecFrozen u.mem → keepR (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvMem (f u).mem ∧ (f u).fs = u.fs :=
  durationSinceGhostFn_replayOn_of_visitedIn hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl)
    hsub_no hw0 hw1 hreal_stub_none hStub hInvLoaded hInvKf hRoInv hLiftVis

theorem f3EmptyDurationSinceGhostHookLs_replayOn_of_visitedIn_of_lrKeep [LibsignalPlacement]
    {InvMem : Memory → Prop} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {mpl : MultiPlacement} {stubPc : BitVec 64}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mpl.base 1))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hRoInv : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      RoDataAt mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (mpl.base 1)) sf →
      Steps P_real (u.setPC (mpl.base 1)) sf) :
    let f := f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1)
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvMem (f u).mem ∧ (f u).fs = u.fs :=
  durationSinceGhostFnLs_replayOn_of_visitedIn_of_lrKeep hpl emptyStdProg_svc hsvc_sub
    (fun _ _ => rfl) hsub_no hw0 hw1 hKeep hreal_stub_none hStub hInvLoaded hInvKf hRoInv hLiftVis

theorem f3EmptyDurationSinceHullGhostHookLs_replayOn_of_visitedIn_of_lrKeep [LibsignalPlacement]
    {InvMem : Memory → Prop} {keepR : BitVec 64 → Bool} {P_real : Program}
    {mpl : MultiPlacement} {stubPc : BitVec 64} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl) (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen)
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (hullBase + subTimespecByteLen))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      (durationSinceHullProg mpl).CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hRoInv : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      RoDataAt mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (hullBase + subTimespecByteLen)) sf →
      Steps P_real (u.setPC (hullBase + subTimespecByteLen)) sf) :
    let f := f3EmptyDurationSinceHullGhostHookLs keepR mpl hullBase
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvMem (f u).mem ∧ (f u).fs = u.fs := by
  dsimp only; unfold f3EmptyDurationSinceHullGhostHookLs
  rw [← hb1] at hStub hLiftVis ⊢
  refine f3EmptyDurationSinceGhostHookLs_replayOn_of_visitedIn_of_lrKeep hpl
    (durationSinceHullProg_svc mpl) (durationSinceHullProg_externAt_none mpl)
    (durationSinceHullProg_hasWords_subTimespec mpl) ?_
    hKeep hreal_stub_none hStub hInvLoaded hInvKf hRoInv hLiftVis
  rw [hb1, ← hb0]; exact durationSinceHullProg_hasWords_durationSince mpl

theorem f3EmptyDurationSinceGhostHook_replaysS_of_visitedIn
    {InvMem : Memory → Prop} {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {mpl : MultiPlacement} {stubPc : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyDurationSinceGhostHook (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1)))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hpl : timeMultiLib.Placeable mpl) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mpl.base 1))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hRoInv : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      RoDataAt mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (mpl.base 1)) sf →
      Steps P_real (u.setPC (mpl.base 1)) sf) :
    GhostExternReplaysS keepR (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyDurationSinceGhostHook_replayOn_of_visitedIn hpl hsvc_sub hsub_no hw0 hw1
    hreal_stub_none hStub hInvLoaded hInvKf hRoInv hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv; ⟨hs, hfr', hinv'⟩⟩

theorem f3EmptyDurationSinceGhostHookLs_replaysS_of_visitedIn_of_lrKeep [LibsignalPlacement]
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop} {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {mpl : MultiPlacement} {stubPc : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1)))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hpl : timeMultiLib.Placeable mpl) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mpl.base 1))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hRoInv : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      RoDataAt mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (mpl.base 1)) sf →
      Steps P_real (u.setPC (mpl.base 1)) sf) :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyDurationSinceGhostHookLs_replayOn_of_visitedIn_of_lrKeep hpl hsvc_sub
    hsub_no hw0 hw1 hKeep hreal_stub_none hStub hInvLoaded hInvKf hRoInv hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv; ⟨hs, hfr', hinv'⟩⟩

theorem f3EmptyDurationSinceGhostHookLs_replaysOn_single_stub_of_visitedIn_of_lrKeep
    [LibsignalPlacement] (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop} {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {mpl : MultiPlacement} {s0 sf : State} {stubPc : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1)))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, Steps P_ghost s0 u → Steps P_ghost (f u) sf → u.pc = pc →
        u.status = .Running → (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem → InvMem u.mem →
        ExecFrozen (f u).mem ∧ InvMem (f u).mem)
    (hpl : timeMultiLib.Placeable mpl) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mpl.base 1))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hRoInv : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      RoDataAt mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hLiftVis : ∀ u sf' : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (mpl.base 1)) sf' →
      Steps P_real (u.setPC (mpl.base 1)) sf') :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  have hRep := f3EmptyDurationSinceGhostHookLs_replayOn_of_visitedIn_of_lrKeep hpl hsvc_sub
    hsub_no hw0 hw1 hKeep hreal_stub_none hStub hInvLoaded hInvKf hRoInv hLiftVis
  exact ghostExternReplaysOn_of_single_stub hghost_stub hother hreal_pres
    ⟨hRep.1, fun u _ _ hpc hrun hnoex _ hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv; ⟨hs, hfr', hinv'⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostLs
