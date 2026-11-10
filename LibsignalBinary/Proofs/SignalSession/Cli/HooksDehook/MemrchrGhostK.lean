/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostLifts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# `W`-Independent Ghost `memrchr` Hook & `GhostExternReplaysOn` / `StepsVisitedIn` Bridge (`HooksDehook.MemrchrGhostK`)

Card **R2-b** companion module to `HooksDehook.MemrchrGhost` (mirroring `HooksDehook.BcmpGhostK`):

1. **`W`-Independent Ghost Hooks (`f3EmptyMemrchrGhostHook{Ls,,K}` & `f3PureMemrchrGhostHook{Ls,,K}`):**
   - Defined with `F3AllocStdinGhostHooks.f3LinkedCallHook` at `P_real := emptyStdProg` (`= Program.ofSvc
     Syscall.standard`) and the `W`-independent fallback `memrchrHook`, so zero `W : CliHooks`
     parameters appear.
   - `f3PureMemrchrGhostHook{Ls,,K}` further fixes `P_sub := pureWordsProg entryTarget coreMemrchrWords`
     (`65` words = `260` B, `REV-MRO` card-c note), discharging all `P_sub` hypotheses unconditionally
     (including hypothesis-free `VmPreserved`).
2. **Variant (i) — Zero Panic Externs, No K4 Needed:**
   Under `masterMemrchrSpec.pre` (`bs.length < 2 ^ 64`), the two `bl slice_index_fail` panic blocks at
   `+0x104` / `+0x118` sit outside the `260` B prefix `coreMemrchrWords` and are never fetched, so
   `P_sub.externAt? pc = none` holds and standard `LinkedCallHookOn` +
   `h2fsgen_real_subroutine_run_visitedIn_of_stripS` apply directly without K4.
3. **Direct `P_real` Replay (`GhostExternReplaysOn` / `GhostExternReplaysS`) & Stock-Safe `StepsVisitedIn` Bridges:**
   - Route `β′` (`memrchrGhostFnLs` / `f3EmptyMemrchrGhostHookLs` / `f3PureMemrchrGhostHookLs`) discharges
     `keepR (u.readReg64 .lr) = false` automatically from `hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false`
     (`K3`), requiring zero per-call `lr` premises.
   - Placement-free `K` (`memrchrGhostFnK` / `f3EmptyMemrchrGhostHookK` / `f3PureMemrchrGhostHookK`)
     discharges `keepR (u.readReg64 .lr) = false` unconditionally from `hnoex`.
   - Raw plain (`memrchrGhostFn` / `f3EmptyMemrchrGhostHook` / `f3PureMemrchrGhostHook`) takes
     `keepR (u.readReg64 .lr) = false` at call sites.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostK

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (memrchrHook)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits OomPreserved PoolPreserved RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Memrchr (cliMemrchrSpec)
open LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO (coreMemrchrWords)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (memrchrSpecRO)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_linkedCallHook
  ghostExternReplaysOn_of_single_stub
  ghostExternReplaysS_of_single_stub
  linkedCallHook_activeRealPre_of_noException
  linkedCallHook_fs_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  withLsRet subroutine_ok_withLsRet withLsRet_pre_setPC withLsRet_outcome_setPC
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (withExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg f3LinkedCallHook_const_eq_linkedCallHook
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det h2fsgen_real_subroutine_run_visitedIn_of_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrCode (
  masterMemrchrSpec memrchrSpecK
  specStripSInvariant_masterMemrchr specStripSInvariant_masterMemrchrK
  pureWordsProg_memrchr_hasWords
  subroutine_ok_masterMemrchr_of_hasWords
  subroutine_ok_masterMemrchrK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhost (
  memrchrGhostFnLs memrchrGhostFn memrchrGhostFnK
  specStripSInvariant_masterMemrchrLs
  specPreservesFsTrace_masterMemrchr specPreservesFsTrace_masterMemrchrLs specPreservesFsTrace_masterMemrchrK
  masterMemrchr_pre_setPC masterMemrchrK_pre_setPC
  masterMemrchr_outcome_setPC masterMemrchrK_outcome_setPC
  memrchrGhostFnLs_masterLs_ok memrchrGhostFn_master_ok memrchrGhostFnK_masterK_ok
  memrchrGhostFnLs_vmPreserved memrchrGhostFn_vmPreserved memrchrGhostFnK_vmPreserved
  memrchrGhostFnLs_oomPoolPreserved memrchrGhostFn_oomPoolPreserved memrchrGhostFnK_oomPoolPreserved
  memrchrGhostFnLs_oracle memrchrGhostFn_oracle memrchrGhostFnK_oracle
  memrchrGhostFnLs_trace memrchrGhostFn_trace memrchrGhostFnK_trace
  memrchrGhostFnLs_lsRetAddr624_of_noException
  memrchrGhostFnLs_keepLr_false_of_noException
  memrchrGhostFnLs_of_not_lsRetAddr624
  memrchrGhostFnK_keepLr_false_of_noException
  memrchrGhostFn_of_keepLr_true memrchrGhostFnK_of_keepLr_true
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostLifts (
  memrchrGhostFnK_masterLs_ok
  memrchrGhostFnLs_mainHopsMemrchr_ok memrchrGhostFnLs_mainHopsMemrchr_extHookStack_ok
  memrchrGhostFnLs_mainHopsMemrchr_budget_ok memrchrGhostFnLs_mainHopsMemrchr_budget_extHookStack_ok
  memrchrGhostFnLs_mainHopsMemrchr_withAlloc_ok memrchrGhostFnLs_mainHopsMemrchr_budget_withAlloc_ok
  memrchrGhostFnLs_memrchrRO_ok memrchrGhostFnLs_memrchrRO_extHookStack_ok
  memrchrGhostFnLs_memrchrRO_budget_ok memrchrGhostFnLs_memrchrRO_budget_extHookStack_ok
  memrchrGhostFnLs_memrchrRO_withAlloc_ok memrchrGhostFnLs_memrchrRO_budget_withAlloc_ok
  memrchrGhostFnLs_cliMemrchr_ok memrchrGhostFnLs_cliMemrchr_budget_ok
  memrchrGhostFnLs_cliMemrchr_withAlloc_ok memrchrGhostFnLs_cliMemrchr_budget_withAlloc_ok
  memrchrGhostFnLs_cliExtMemrchr_ok memrchrGhostFnLs_cliExtMemrchr_keepsFs_ok
  memrchrGhostFnLs_cliExtMemrchr_budget_ok
  memrchrGhostFnLs_cliExtMemrchr_withAlloc_ok memrchrGhostFnLs_cliExtMemrchr_budget_withAlloc_ok
  memrchrGhostFn_mainHopsMemrchr_ok memrchrGhostFn_mainHopsMemrchr_budget_ok
  memrchrGhostFn_mainHopsMemrchr_withAlloc_ok memrchrGhostFn_mainHopsMemrchr_budget_withAlloc_ok
  memrchrGhostFn_memrchrRO_ok memrchrGhostFn_memrchrRO_budget_ok
  memrchrGhostFn_memrchrRO_withAlloc_ok memrchrGhostFn_memrchrRO_budget_withAlloc_ok
  memrchrGhostFn_cliMemrchr_ok memrchrGhostFn_cliMemrchr_budget_ok
  memrchrGhostFn_cliExtMemrchr_ok memrchrGhostFn_cliExtMemrchr_keepsFs_ok
  memrchrGhostFn_cliExtMemrchr_budget_ok
  memrchrGhostFnK_mainHopsMemrchrK_ok memrchrGhostFnK_mainHopsMemrchrK_budget_ok
  memrchrGhostFnK_mainHopsMemrchrK_withAlloc_ok memrchrGhostFnK_mainHopsMemrchrK_budget_withAlloc_ok
  memrchrGhostFnK_memrchrROK_ok memrchrGhostFnK_memrchrROK_budget_ok
  memrchrGhostFnK_memrchrROK_withAlloc_ok memrchrGhostFnK_memrchrROK_budget_withAlloc_ok
  memrchrGhostFnK_cliMemrchrK_ok memrchrGhostFnK_cliMemrchrK_budget_ok
  memrchrGhostFnK_cliExtMemrchrK_ok memrchrGhostFnK_cliExtMemrchrK_budget_ok
  memrchrGhostFnLs_any_keepsFs_ok memrchrGhostFnLs_any_withOomPoolPreserved_ok
  memrchrGhostFnLs_any_execFrozen_ok
  memrchrGhostFn_any_keepsFs_ok memrchrGhostFn_any_withOomPoolPreserved_ok
  memrchrGhostFn_any_execFrozen_ok memrchrGhostFn_any_memrchrSpecK_ok
  memrchrGhostFnK_any_keepsFs_ok memrchrGhostFnK_any_withOomPoolPreserved_ok
  memrchrGhostFnK_any_execFrozen_ok
)

/-! ## 1. `W`-Independent Ghost `memrchr` Hook Definitions & Equalities -/

/-- **Route `β′` primary `W`-independent `memrchr` ghost hook (`P_real := emptyStdProg`):** wraps
    `withLsRet masterMemrchrSpec` via `f3LinkedCallHook` with fallback `memrchrHook`. -/
@[expose] noncomputable def f3EmptyMemrchrGhostHookLs [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keepR emptyStdProg P_sub entryTarget
    (fun _ _ => withLsRet masterMemrchrSpec) memrchrHook

/-- Plain `W`-independent `memrchr` ghost hook (`P_real := emptyStdProg`) wrapping
    `masterMemrchrSpec`. -/
@[expose] noncomputable def f3EmptyMemrchrGhostHook
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keepR emptyStdProg P_sub entryTarget
    (fun _ _ => masterMemrchrSpec) memrchrHook

/-- Placement-free `K`-narrowed (`memrchrSpecK keepR masterMemrchrSpec`) `W`-independent `memrchr`
    ghost hook (`P_real := emptyStdProg`). -/
@[expose] noncomputable def f3EmptyMemrchrGhostHookK
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keepR emptyStdProg P_sub entryTarget
    (fun _ _ => memrchrSpecK keepR masterMemrchrSpec) memrchrHook

/-- Concrete `P_sub := pureWordsProg entryTarget coreMemrchrWords` (`65` w / `260` B) specialization
    of `f3EmptyMemrchrGhostHookLs` (`REV-MRO` card-c note). -/
noncomputable abbrev f3PureMemrchrGhostHookLs [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) : State → State :=
  f3EmptyMemrchrGhostHookLs keepR (pureWordsProg entryTarget coreMemrchrWords) entryTarget

/-- Concrete `P_sub := pureWordsProg entryTarget coreMemrchrWords` specialization of
    `f3EmptyMemrchrGhostHook`. -/
noncomputable abbrev f3PureMemrchrGhostHook
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) : State → State :=
  f3EmptyMemrchrGhostHook keepR (pureWordsProg entryTarget coreMemrchrWords) entryTarget

/-- Concrete `P_sub := pureWordsProg entryTarget coreMemrchrWords` specialization of
    `f3EmptyMemrchrGhostHookK`. -/
noncomputable abbrev f3PureMemrchrGhostHookK
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) : State → State :=
  f3EmptyMemrchrGhostHookK keepR (pureWordsProg entryTarget coreMemrchrWords) entryTarget

theorem f3EmptyMemrchrGhostHookLs_eq [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget =
      memrchrGhostFnLs keepR emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keepR emptyStdProg P_sub entryTarget
    (withLsRet masterMemrchrSpec) memrchrHook

theorem f3EmptyMemrchrGhostHook_eq
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyMemrchrGhostHook keepR P_sub entryTarget =
      memrchrGhostFn keepR emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keepR emptyStdProg P_sub entryTarget
    masterMemrchrSpec memrchrHook

theorem f3EmptyMemrchrGhostHookK_eq
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyMemrchrGhostHookK keepR P_sub entryTarget =
      memrchrGhostFnK keepR emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keepR emptyStdProg P_sub entryTarget
    (memrchrSpecK keepR masterMemrchrSpec) memrchrHook

/-! ## 2. State / Frame / `lr` Properties (`P_real` Hypotheses Discharged Unconditionally) -/

theorem f3EmptyMemrchrGhostHookLs_fs [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keepR emptyStdProg P_sub entryTarget _ memrchrHook s0

theorem f3EmptyMemrchrGhostHook_fs
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyMemrchrGhostHook keepR P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keepR emptyStdProg P_sub entryTarget _ memrchrHook s0

theorem f3EmptyMemrchrGhostHookK_fs
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keepR emptyStdProg P_sub entryTarget _ memrchrHook s0

theorem f3EmptyMemrchrGhostHookLs_fsT [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget) :=
  f3LinkedCallHook_fsT keepR emptyStdProg P_sub entryTarget _ memrchrHook

theorem f3EmptyMemrchrGhostHook_fsT
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyMemrchrGhostHook keepR P_sub entryTarget) :=
  f3LinkedCallHook_fsT keepR emptyStdProg P_sub entryTarget _ memrchrHook

theorem f3EmptyMemrchrGhostHookK_fsT
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget) :=
  f3LinkedCallHook_fsT keepR emptyStdProg P_sub entryTarget _ memrchrHook

theorem f3EmptyMemrchrGhostHookLs_vmPreserved [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    VmPreserved s0 (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget s0) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHook_vmPreserved
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    VmPreserved s0 (f3EmptyMemrchrGhostHook keepR P_sub entryTarget s0) := by
  rw [f3EmptyMemrchrGhostHook_eq]
  exact memrchrGhostFn_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHookK_vmPreserved
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    VmPreserved s0 (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget s0) := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

/-- Hypothesis-free `VmPreserved` (`hvm`) for `f3PureMemrchrGhostHookLs` (`REV-MRO` card-c note). -/
theorem f3PureMemrchrGhostHookLs_vmPreserved [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) (s0 : State) :
    VmPreserved s0 (f3PureMemrchrGhostHookLs keepR entryTarget s0) :=
  f3EmptyMemrchrGhostHookLs_vmPreserved rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget) s0

/-- Hypothesis-free `VmPreserved` (`hvm`) for `f3PureMemrchrGhostHook`. -/
theorem f3PureMemrchrGhostHook_vmPreserved
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) (s0 : State) :
    VmPreserved s0 (f3PureMemrchrGhostHook keepR entryTarget s0) :=
  f3EmptyMemrchrGhostHook_vmPreserved rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget) s0

/-- Hypothesis-free `VmPreserved` (`hvm`) for `f3PureMemrchrGhostHookK`. -/
theorem f3PureMemrchrGhostHookK_vmPreserved
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) (s0 : State) :
    VmPreserved s0 (f3PureMemrchrGhostHookK keepR entryTarget s0) :=
  f3EmptyMemrchrGhostHookK_vmPreserved rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget) s0

theorem f3EmptyMemrchrGhostHookLs_oomPoolPreserved [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    OomPreserved s0 (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget s0) ∧
      PoolPreserved s0 (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget s0) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_oomPoolPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHook_oomPoolPreserved
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    OomPreserved s0 (f3EmptyMemrchrGhostHook keepR P_sub entryTarget s0) ∧
      PoolPreserved s0 (f3EmptyMemrchrGhostHook keepR P_sub entryTarget s0) := by
  rw [f3EmptyMemrchrGhostHook_eq]
  exact memrchrGhostFn_oomPoolPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHookK_oomPoolPreserved
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    OomPreserved s0 (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget s0) ∧
      PoolPreserved s0 (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget s0) := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_oomPoolPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHookLs_oracle [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget s0).oracle = s0.oracle := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_oracle rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHook_oracle
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    (f3EmptyMemrchrGhostHook keepR P_sub entryTarget s0).oracle = s0.oracle := by
  rw [f3EmptyMemrchrGhostHook_eq]
  exact memrchrGhostFn_oracle rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHookK_oracle
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget s0).oracle = s0.oracle := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_oracle rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHookLs_trace [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_trace rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHook_trace
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    (f3EmptyMemrchrGhostHook keepR P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyMemrchrGhostHook_eq]
  exact memrchrGhostFn_trace rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHookK_trace
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (s0 : State) :
    (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_trace rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemrchrGhostHookLs_lsRetAddr624_of_noException [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg, (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) := by
  rw [f3EmptyMemrchrGhostHookLs_eq] at hnoex
  exact memrchrGhostFnLs_lsRetAddr624_of_noException hnoex

theorem f3EmptyMemrchrGhostHookLs_keepLr_false_of_noException [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {u : State}
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hnoex : ∀ msg, (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).status ≠ .Exception msg) :
    keepR (u.readReg64 .lr) = false := by
  rw [f3EmptyMemrchrGhostHookLs_eq] at hnoex
  exact memrchrGhostFnLs_keepLr_false_of_noException hKeep hnoex

theorem f3EmptyMemrchrGhostHookLs_of_not_lsRetAddr624 [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hnlr : ¬ LsRetAddr624 (s0.readReg64 .lr)) :
    f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_of_not_lsRetAddr624 hnlr

theorem f3EmptyMemrchrGhostHookK_keepLr_false_of_noException
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg, (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).status ≠ .Exception msg) :
    keepR (u.readReg64 .lr) = false := by
  rw [f3EmptyMemrchrGhostHookK_eq] at hnoex
  exact memrchrGhostFnK_keepLr_false_of_noException hnoex

theorem f3EmptyMemrchrGhostHook_of_keepLr_true
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hActPre : ActiveRealPre masterMemrchrSpec s0)
    (hlr_in : keepR (s0.readReg64 .lr) = true) :
    f3EmptyMemrchrGhostHook keepR P_sub entryTarget s0 = memrchrHook s0 := by
  rw [f3EmptyMemrchrGhostHook_eq]
  exact memrchrGhostFn_of_keepLr_true hActPre hlr_in

theorem f3EmptyMemrchrGhostHookK_of_keepLr_true
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hlr_in : keepR (s0.readReg64 .lr) = true) :
    f3EmptyMemrchrGhostHookK keepR P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_of_keepLr_true hlr_in


/-! ## 3. Consumer `HookOk` Forwarding (`P_real` Discharged; `f3Pure*` Also Discharges `P_sub`) -/

section HookOkForwarding

variable {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget coreMemrchrWords)

include hsvc_sub hsub_no hwords

-- 3.1 Route `β′` (`withLsRet`, `16 ≤ stk ≤ 2 ^ 64` + `extHookStack`) on `f3EmptyMemrchrGhostHookLs`:

theorem f3EmptyMemrchrGhostHookLs_masterLs_ok [LibsignalPlacement] :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget) (withLsRet masterMemrchrSpec) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_masterLs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemrchrGhostHookLs_mainHopsMemrchr_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_mainHopsMemrchr_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    stk hlo hhi

theorem f3EmptyMemrchrGhostHookLs_mainHopsMemrchr_extHookStack_ok [LibsignalPlacement] :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack)) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_mainHopsMemrchr_extHookStack_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords

theorem f3EmptyMemrchrGhostHookLs_mainHopsMemrchr_budget_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_mainHopsMemrchr_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    stk hlo hhi

theorem f3EmptyMemrchrGhostHookLs_mainHopsMemrchr_budget_extHookStack_ok [LibsignalPlacement] :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_mainHopsMemrchr_budget_extHookStack_ok rfl hsvc_sub (fun _ _ => rfl)
    hsub_no hwords

theorem f3EmptyMemrchrGhostHookLs_mainHopsMemrchr_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (withAlloc (M := M) A lim
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_mainHopsMemrchr_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    A lim stk hlo hhi

theorem f3EmptyMemrchrGhostHookLs_mainHopsMemrchr_budget_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withAlloc (M := M) A lim (withLsRet (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_mainHopsMemrchr_budget_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords A lim stk hlo hhi

theorem f3EmptyMemrchrGhostHookLs_memrchrRO_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (memrchrSpecRO stk)) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_memrchrRO_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk hlo hhi

theorem f3EmptyMemrchrGhostHookLs_memrchrRO_extHookStack_ok [LibsignalPlacement] :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (memrchrSpecRO extHookStack)) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_memrchrRO_extHookStack_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemrchrGhostHookLs_memrchrRO_budget_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (withVmPreserved (memrchrSpecRO stk))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_memrchrRO_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk hlo
    hhi

theorem f3EmptyMemrchrGhostHookLs_memrchrRO_budget_extHookStack_ok [LibsignalPlacement] :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_memrchrRO_budget_extHookStack_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords

theorem f3EmptyMemrchrGhostHookLs_memrchrRO_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (withAlloc (M := M) A lim (memrchrSpecRO stk))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_memrchrRO_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords A lim
    stk hlo hhi

theorem f3EmptyMemrchrGhostHookLs_memrchrRO_budget_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withAlloc (M := M) A lim (withLsRet (withVmPreserved (memrchrSpecRO stk)))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_memrchrRO_budget_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    A lim stk hlo hhi

theorem f3EmptyMemrchrGhostHookLs_cliMemrchr_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (cliMemrchrSpec stk)) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_cliMemrchr_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk hlo hhi

theorem f3EmptyMemrchrGhostHookLs_cliMemrchr_budget_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (withVmPreserved (cliMemrchrSpec stk))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_cliMemrchr_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk hlo
    hhi

theorem f3EmptyMemrchrGhostHookLs_cliMemrchr_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (withAlloc (M := M) A lim (cliMemrchrSpec stk))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_cliMemrchr_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords A lim
    stk hlo hhi

theorem f3EmptyMemrchrGhostHookLs_cliMemrchr_budget_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withAlloc (M := M) A lim (withLsRet (withVmPreserved (cliMemrchrSpec stk)))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_cliMemrchr_budget_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords A lim stk hlo hhi

theorem f3EmptyMemrchrGhostHookLs_cliExtMemrchr_ok [LibsignalPlacement] :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet CryptoVerification.SignalSession.CliExt.memrchrSpec) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_cliExtMemrchr_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemrchrGhostHookLs_cliExtMemrchr_keepsFs_ok [LibsignalPlacement] :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (keepsFs CryptoVerification.SignalSession.CliExt.memrchrSpec)) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_cliExtMemrchr_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemrchrGhostHookLs_cliExtMemrchr_budget_ok [LibsignalPlacement] :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec)) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_cliExtMemrchr_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemrchrGhostHookLs_cliExtMemrchr_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withLsRet (withAlloc (M := M) A lim
        CryptoVerification.SignalSession.CliExt.memrchrSpec)) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_cliExtMemrchr_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    A lim

theorem f3EmptyMemrchrGhostHookLs_cliExtMemrchr_budget_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget)
      (withAlloc (M := M) A lim
        (withLsRet (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec))) := by
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_cliExtMemrchr_budget_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords A lim

-- 3.2 Plain & `K` forwarding on `f3EmptyMemrchrGhostHook` / `f3EmptyMemrchrGhostHookK`:

theorem f3EmptyMemrchrGhostHook_master_ok :
    HookOk (f3EmptyMemrchrGhostHook keepR P_sub entryTarget) masterMemrchrSpec := by
  rw [f3EmptyMemrchrGhostHook_eq]
  exact memrchrGhostFn_master_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemrchrGhostHook_mainHopsMemrchr_budget_ok
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHook keepR P_sub entryTarget)
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)) := by
  rw [f3EmptyMemrchrGhostHook_eq]
  exact memrchrGhostFn_mainHopsMemrchr_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    stk hlo hhi

theorem f3EmptyMemrchrGhostHook_memrchrRO_budget_ok
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHook keepR P_sub entryTarget)
      (withVmPreserved (memrchrSpecRO stk)) := by
  rw [f3EmptyMemrchrGhostHook_eq]
  exact memrchrGhostFn_memrchrRO_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk hlo hhi

theorem f3EmptyMemrchrGhostHook_cliExtMemrchr_budget_ok :
    HookOk (f3EmptyMemrchrGhostHook keepR P_sub entryTarget)
      (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec) := by
  rw [f3EmptyMemrchrGhostHook_eq]
  exact memrchrGhostFn_cliExtMemrchr_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemrchrGhostHookK_masterK_ok :
    HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget)
      (memrchrSpecK keepR masterMemrchrSpec) := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_masterK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemrchrGhostHookK_masterLs_ok [LibsignalPlacement]
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false) :
    HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget) (withLsRet masterMemrchrSpec) := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_masterLs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords hKeep

theorem f3EmptyMemrchrGhostHookK_mainHopsMemrchrK_budget_ok
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget)
      (memrchrSpecK keepR
        (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_mainHopsMemrchrK_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    stk hlo hhi

theorem f3EmptyMemrchrGhostHookK_mainHopsMemrchrK_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget)
      (memrchrSpecK keepR (withAlloc (M := M) A lim
        (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)))) := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_mainHopsMemrchrK_budget_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords A lim stk hlo hhi

theorem f3EmptyMemrchrGhostHookK_memrchrROK_budget_ok
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget)
      (memrchrSpecK keepR (withVmPreserved (memrchrSpecRO stk))) := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_memrchrROK_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk hlo
    hhi

theorem f3EmptyMemrchrGhostHookK_memrchrROK_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget)
      (memrchrSpecK keepR (withAlloc (M := M) A lim (withVmPreserved (memrchrSpecRO stk)))) := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_memrchrROK_budget_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    A lim stk hlo hhi

theorem f3EmptyMemrchrGhostHookK_cliExtMemrchrK_budget_ok :
    HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget)
      (memrchrSpecK keepR (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec)) := by
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_cliExtMemrchrK_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

omit hsvc_sub hsub_no hwords in
theorem f3EmptyMemrchrGhostHookLs_any_keepsFs_ok [LibsignalPlacement] {α : Type} {spec : Spec α}
    (hh : HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget) spec) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget) spec.keepsFs := by
  rw [f3EmptyMemrchrGhostHookLs_eq] at hh ⊢
  exact memrchrGhostFnLs_any_keepsFs_ok hh

theorem f3EmptyMemrchrGhostHookLs_any_withOomPoolPreserved_ok [LibsignalPlacement]
    {α : Type} {spec : Spec α}
    (hh : HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget) spec) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget) (withOomPoolPreserved spec) := by
  rw [f3EmptyMemrchrGhostHookLs_eq] at hh ⊢
  exact memrchrGhostFnLs_any_withOomPoolPreserved_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    hh

omit hsvc_sub hsub_no hwords in
theorem f3EmptyMemrchrGhostHookLs_any_execFrozen_ok [LibsignalPlacement] {α : Type} {spec : Spec α}
    (hh : HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget) spec) :
    HookOk (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget) (withExecFrozen spec) := by
  rw [f3EmptyMemrchrGhostHookLs_eq] at hh ⊢
  exact memrchrGhostFnLs_any_execFrozen_ok hh

omit hsvc_sub hsub_no hwords in
theorem f3EmptyMemrchrGhostHook_any_keepsFs_ok {α : Type} {spec : Spec α}
    (hh : HookOk (f3EmptyMemrchrGhostHook keepR P_sub entryTarget) spec) :
    HookOk (f3EmptyMemrchrGhostHook keepR P_sub entryTarget) spec.keepsFs := by
  rw [f3EmptyMemrchrGhostHook_eq] at hh ⊢
  exact memrchrGhostFn_any_keepsFs_ok hh

omit hsvc_sub hsub_no hwords in
theorem f3EmptyMemrchrGhostHook_any_memrchrSpecK_ok {α : Type} {spec : Spec α}
    (hh : HookOk (f3EmptyMemrchrGhostHook keepR P_sub entryTarget) spec) :
    HookOk (f3EmptyMemrchrGhostHook keepR P_sub entryTarget) (memrchrSpecK keepR spec) := by
  rw [f3EmptyMemrchrGhostHook_eq] at hh ⊢
  exact memrchrGhostFn_any_memrchrSpecK_ok hh

omit hsvc_sub hsub_no hwords in
theorem f3EmptyMemrchrGhostHookK_any_keepsFs_ok {α : Type} {spec : Spec α}
    (hh : HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget) spec) :
    HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget) spec.keepsFs := by
  rw [f3EmptyMemrchrGhostHookK_eq] at hh ⊢
  exact memrchrGhostFnK_any_keepsFs_ok hh

theorem f3EmptyMemrchrGhostHookK_any_withOomPoolPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget) spec) :
    HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget) (withOomPoolPreserved spec) := by
  rw [f3EmptyMemrchrGhostHookK_eq] at hh ⊢
  exact memrchrGhostFnK_any_withOomPoolPreserved_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords hh

omit hsvc_sub hsub_no hwords in
theorem f3EmptyMemrchrGhostHookK_any_execFrozen_ok {α : Type} {spec : Spec α}
    (hh : HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget) spec) :
    HookOk (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget) (withExecFrozen spec) := by
  rw [f3EmptyMemrchrGhostHookK_eq] at hh ⊢
  exact memrchrGhostFnK_any_execFrozen_ok hh

end HookOkForwarding

-- 3.3 Hypothesis-free `f3PureMemrchrGhostHookLs` (`P_sub := pureWordsProg`) consumer `HookOk`:

theorem f3PureMemrchrGhostHookLs_masterLs_ok [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) :
    HookOk (f3PureMemrchrGhostHookLs keepR entryTarget) (withLsRet masterMemrchrSpec) :=
  f3EmptyMemrchrGhostHookLs_masterLs_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget)

theorem f3PureMemrchrGhostHookLs_mainHopsMemrchr_ok [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3PureMemrchrGhostHookLs keepR entryTarget)
      (withLsRet (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)) :=
  f3EmptyMemrchrGhostHookLs_mainHopsMemrchr_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget) stk hlo hhi

theorem f3PureMemrchrGhostHookLs_mainHopsMemrchr_budget_ok [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3PureMemrchrGhostHookLs keepR entryTarget)
      (withLsRet (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) :=
  f3EmptyMemrchrGhostHookLs_mainHopsMemrchr_budget_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget) stk hlo hhi

theorem f3PureMemrchrGhostHookLs_mainHopsMemrchr_budget_extHookStack_ok [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) :
    HookOk (f3PureMemrchrGhostHookLs keepR entryTarget)
      (withLsRet (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack))) :=
  f3EmptyMemrchrGhostHookLs_mainHopsMemrchr_budget_extHookStack_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget)

theorem f3PureMemrchrGhostHookLs_mainHopsMemrchr_budget_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3PureMemrchrGhostHookLs keepR entryTarget)
      (withAlloc (M := M) A lim (withLsRet (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)))) :=
  f3EmptyMemrchrGhostHookLs_mainHopsMemrchr_budget_withAlloc_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget) A lim stk hlo hhi

theorem f3PureMemrchrGhostHookLs_memrchrRO_ok [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3PureMemrchrGhostHookLs keepR entryTarget) (withLsRet (memrchrSpecRO stk)) :=
  f3EmptyMemrchrGhostHookLs_memrchrRO_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget) stk hlo hhi

theorem f3PureMemrchrGhostHookLs_memrchrRO_budget_ok [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3PureMemrchrGhostHookLs keepR entryTarget)
      (withLsRet (withVmPreserved (memrchrSpecRO stk))) :=
  f3EmptyMemrchrGhostHookLs_memrchrRO_budget_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget) stk hlo hhi

theorem f3PureMemrchrGhostHookLs_memrchrRO_budget_extHookStack_ok [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) :
    HookOk (f3PureMemrchrGhostHookLs keepR entryTarget)
      (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))) :=
  f3EmptyMemrchrGhostHookLs_memrchrRO_budget_extHookStack_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget)

theorem f3PureMemrchrGhostHookLs_memrchrRO_budget_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (f3PureMemrchrGhostHookLs keepR entryTarget)
      (withAlloc (M := M) A lim (withLsRet (withVmPreserved (memrchrSpecRO stk)))) :=
  f3EmptyMemrchrGhostHookLs_memrchrRO_budget_withAlloc_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget) A lim stk hlo hhi

theorem f3PureMemrchrGhostHookLs_cliExtMemrchr_budget_ok [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) :
    HookOk (f3PureMemrchrGhostHookLs keepR entryTarget)
      (withLsRet (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec)) :=
  f3EmptyMemrchrGhostHookLs_cliExtMemrchr_budget_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget)

theorem f3PureMemrchrGhostHook_master_ok
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) :
    HookOk (f3PureMemrchrGhostHook keepR entryTarget) masterMemrchrSpec :=
  f3EmptyMemrchrGhostHook_master_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget)

theorem f3PureMemrchrGhostHookK_masterK_ok
    (keepR : BitVec 64 → Bool) (entryTarget : BitVec 64) :
    HookOk (f3PureMemrchrGhostHookK keepR entryTarget) (memrchrSpecK keepR masterMemrchrSpec) :=
  f3EmptyMemrchrGhostHookK_masterK_ok rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget)
end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostK
