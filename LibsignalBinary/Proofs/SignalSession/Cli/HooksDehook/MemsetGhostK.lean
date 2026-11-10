/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn -- proof-setup: allow-public-import

/-!
# `W`-Independent K-Convention `memset` Ghost Hook (`HooksDehook.MemsetGhostK`)

Layout-independent, `CliElf`-free (`LibsignalBinary.Cli`-rootable) core for the K-route
`W`-independent `memset` ghost hook (`rev_c1.md` §4b):

1. **`emptyStdProg := Program.ofSvc Syscall.standard`**:
   `rfl`-equal to `ElfSlicesPqOomPlacedInst.hole2_emptyProg`, satisfying `emptyStdProg.svc =
   Syscall.standard` and `∀ pc, emptyStdProg.externAt? pc = none` unconditionally by `rfl`.
2. **`f3EmptyMemsetGhostHook` & `f3EmptyMemsetGhostHookK`**:
   Defined with `F3AllocStdinGhostHooks.f3LinkedCallHook` at `P_real := emptyStdProg` — the exact
   combinator and `P_real` used by `ElfSlicesPqOomH2KHooks.h2k_ghFixedK` for the 7 F3 ghosts —
   with **zero dependence on `W : CliHooks`**, so it can be fixed outside `∀ W` in
   `Block617TransferFixedHyp`.
3. **Extensional Bridge to `memsetGhostHook` / `memsetGhostHookK`**:
   `f3LinkedCallHook_const_eq_linkedCallHook` proves that for any `(γ, tp)`-constant spec
   `fun _ _ => spec` and any `fallback`, `f3LinkedCallHook` equals `linkedCallHook`, giving
   `f3EmptyMemsetGhostHook_eq` and `f3EmptyMemsetGhostHookK_eq` and forwarding all `HookOk`,
   `HookFsTraced`, `VmPreserved`, and `OomPreserved ∧ PoolPreserved` contracts from
   `HooksDehook.MemsetGhost` with **zero `P_real` hypotheses**.
4. **`emptyStdProg` First-Stop Witness & `emptyStdProg → P_real` Guarded Replay Combinators**:
   `f3EmptyMemsetGhostHook_stepsUntil` / `f3EmptyMemsetGhostHookK_stepsUntil` produce the
   `W`-independent `StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget) (f u)` witness,
   and `f3EmptyMemsetGhostHook_replayOn_of_emptyLift` /
   `f3EmptyMemsetGhostHookK_replayOn_of_emptyLift` lift it across any `P_real` (such as
   `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` via the empty-lift hypothesis) behind
   `StubReachesTargetOn InvMem P_real stubPc entryTarget`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK

open Arm64 ProofLib
open VerifiedLibraries.Musl (memsetWordsSym)
open CryptoVerification.LibsignalTripleRatchet (
  sessionMemsetRegionSpec sessionMemsetSpec withStack
)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (session2MemsetExternSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec
)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (memsetSpec)
open LibsignalBinary.Heap (OomPreserved PoolPreserved VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (libcMemsetCliSpec memsetRegionCliSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen
  linkedCallHook real_subroutine_run_of_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  ActiveF3CallPre f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysS_of_single_stub
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  masterMemsetSpec memsetSpecK
  subroutine_ok_masterMemset_of_hasWords subroutine_ok_masterMemsetK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  masterMemset_outcome_setPC masterMemset_pre_setPC
  masterMemsetK_outcome_setPC masterMemsetK_pre_setPC
  memsetGhostHook memsetGhostHookK
  memsetGhostHook_any_memsetSpecK_ok
  memsetGhostHook_cliMemset_budget_ok memsetGhostHook_cliMemset_keepsFs_ok
  memsetGhostHook_cliMemset_ok
  memsetGhostHook_libcMemset_budget_keepsFs_ok memsetGhostHook_libcMemset_budget_ok
  memsetGhostHook_libcMemset_execFrozen_ok memsetGhostHook_libcMemset_keepsFs_ok
  memsetGhostHook_libcMemset_ok memsetGhostHook_libcMemsetCli_ok
  memsetGhostHook_master_ok
  memsetGhostHook_memsetRegion_budget_ok memsetGhostHook_memsetRegion_budget_withStack_keepsFs_ok
  memsetGhostHook_memsetRegion_budget_withStack_ok memsetGhostHook_memsetRegion_execFrozen_ok
  memsetGhostHook_memsetRegion_keepsFs_ok memsetGhostHook_memsetRegion_ok
  memsetGhostHook_memsetRegion_withStack_ok memsetGhostHook_memsetRegionCli_ok
  memsetGhostHook_of_keepLr_true memsetGhostHook_oomPoolPreserved
  memsetGhostHook_session2MemsetExtern_budget_keepsFs_ok
  memsetGhostHook_session2MemsetExtern_budget_ok
  memsetGhostHook_session2MemsetExtern_execFrozen_ok
  memsetGhostHook_session2MemsetExtern_keepsFs_ok memsetGhostHook_session2MemsetExtern_ok
  memsetGhostHook_sessionMemset_execFrozen_ok memsetGhostHook_sessionMemset_keepsFs_ok
  memsetGhostHook_sessionMemset_ok memsetGhostHook_sessionMemsetBudget_keepsFs_ok
  memsetGhostHook_sessionMemsetBudget_ok
  memsetGhostHook_sessionMemsetRegion_execFrozen_ok memsetGhostHook_sessionMemsetRegion_keepsFs_ok
  memsetGhostHook_sessionMemsetRegion_ok memsetGhostHook_sessionMemsetRegion_withStack_ok
  memsetGhostHook_sessionMemsetRegionBudget_ok
  memsetGhostHook_sessionMemsetRegionBudget_withStack_keepsFs_ok
  memsetGhostHook_sessionMemsetRegionBudget_withStack_ok
  memsetGhostHook_trace memsetGhostHook_vmPreserved
  memsetGhostHookK_cliMemsetK_budget_ok memsetGhostHookK_cliMemsetK_keepsFs_ok
  memsetGhostHookK_cliMemsetK_ok
  memsetGhostHookK_keepLr_false_of_noException
  memsetGhostHookK_libcMemsetCliK_ok memsetGhostHookK_libcMemsetK_budget_keepsFs_ok
  memsetGhostHookK_libcMemsetK_budget_ok memsetGhostHookK_libcMemsetK_keepsFs_ok
  memsetGhostHookK_libcMemsetK_ok
  memsetGhostHookK_masterK_ok
  memsetGhostHookK_memsetRegionCliK_ok memsetGhostHookK_memsetRegionK_budget_ok
  memsetGhostHookK_memsetRegionK_budget_withStack_keepsFs_ok
  memsetGhostHookK_memsetRegionK_budget_withStack_ok memsetGhostHookK_memsetRegionK_keepsFs_ok
  memsetGhostHookK_memsetRegionK_ok
  memsetGhostHookK_of_keepLr_true memsetGhostHookK_oomPoolPreserved
  memsetGhostHookK_session2MemsetExternK_budget_keepsFs_ok
  memsetGhostHookK_session2MemsetExternK_budget_ok
  memsetGhostHookK_session2MemsetExternK_keepsFs_ok memsetGhostHookK_session2MemsetExternK_ok
  memsetGhostHookK_sessionMemsetBudgetK_keepsFs_ok memsetGhostHookK_sessionMemsetBudgetK_ok
  memsetGhostHookK_sessionMemsetK_keepsFs_ok memsetGhostHookK_sessionMemsetK_ok
  memsetGhostHookK_sessionMemsetRegionBudgetK_ok
  memsetGhostHookK_sessionMemsetRegionBudgetK_withStack_keepsFs_ok
  memsetGhostHookK_sessionMemsetRegionBudgetK_withStack_ok
  memsetGhostHookK_sessionMemsetRegionK_keepsFs_ok memsetGhostHookK_sessionMemsetRegionK_ok
  memsetGhostHookK_trace memsetGhostHookK_vmPreserved
  specPreservesFsTrace_masterMemset specPreservesFsTrace_masterMemsetK
  specStripSInvariant_masterMemset specStripSInvariant_masterMemsetK
  withExecFrozen
)

/-! ## 1. `emptyStdProg` & Generic `f3LinkedCallHook` ↔ `linkedCallHook` Bridge -/

/-- `W`-independent empty-extern `Syscall.standard` program (`rfl`-equal to
    `ElfSlicesPqOomPlacedInst.hole2_emptyProg`). -/
@[expose] def emptyStdProg : Program := Program.ofSvc Syscall.standard

@[simp]
theorem emptyStdProg_svc : emptyStdProg.svc = Syscall.standard := rfl

@[simp]
theorem emptyStdProg_externAt_none (pc : BitVec 64) : emptyStdProg.externAt? pc = none := rfl

/-- For a `(γ, tp)`-constant `Spec`, `ActiveF3CallPre (fun _ _ => spec)` is logically equivalent to
    `ActiveRealPre spec` because both `GhostName` (`default`) and `BitVec 64` (`0#64`) are
    inhabited. -/
theorem activeF3CallPre_const_iff {α : Type} (spec : Spec α) (s0 : State) :
    ActiveF3CallPre (fun _ _ => spec) s0 ↔ ActiveRealPre spec s0 := by
  constructor
  · rintro ⟨hrun, hsp, _, _, x, R, hpre⟩
    exact ⟨hrun, hsp, x, R, hpre⟩
  · rintro ⟨hrun, hsp, x, R, hpre⟩
    exact ⟨hrun, hsp, default, 0#64, x, R, hpre⟩

/-- Whenever `specOf` does not depend on `(γ, tp)` (`fun _ _ => spec`), `f3LinkedCallHook` is
    extensionally equal to `linkedCallHook` for **every** `fallback` (both wrap `fallback` in
    `keepFsTrace` on the non-`ActiveRealRun` branch). -/
theorem f3LinkedCallHook_const_eq_linkedCallHook {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) (fallback : State → State) :
    f3LinkedCallHook keep P_real P_sub entryTarget (fun _ _ => spec) fallback =
      linkedCallHook keep P_real P_sub entryTarget spec fallback := by
  classical
  funext s0
  unfold f3LinkedCallHook linkedCallHook
  have hiff : ActiveF3CallPre (fun _ _ => spec) s0 ↔ ActiveRealPre spec s0 :=
    activeF3CallPre_const_iff spec s0
  by_cases hPre : ActiveRealPre spec s0
  · have hPreF3 : ActiveF3CallPre (fun _ _ => spec) s0 := hiff.mpr hPre
    simp only [hPreF3, hPre, ↓reduceDIte]
  · have hNotPreF3 : ¬ ActiveF3CallPre (fun _ _ => spec) s0 := fun h => hPre (hiff.mp h)
    simp [hNotPreF3, hPre]

/-! ## 2. `W`-Independent K-Convention `memset` Ghost Hook Definitions & Equalities -/

/-- Plain `W`-independent K-convention `memset` ghost hook (`P_real := emptyStdProg =
    Program.ofSvc Syscall.standard`), parametric in `keep`, `P_sub` (e.g. `f3TrialRxProg`), and
    `entryTarget` (`mmpl.base 21`). -/
@[expose] noncomputable def f3EmptyMemsetGhostHook
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget
    (fun _ _ => masterMemsetSpec) hookMemset

/-- `K`-narrowed (`memsetSpecK keep masterMemsetSpec`, `rfl`-equal to
    `h2k_withKeepLrFalse keep masterMemsetSpec`) `W`-independent K-convention `memset` ghost hook. -/
@[expose] noncomputable def f3EmptyMemsetGhostHookK
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget
    (fun _ _ => memsetSpecK keep masterMemsetSpec) hookMemset

/-- `f3EmptyMemsetGhostHook` equals `memsetGhostHook` specialized to `P_real := emptyStdProg`. -/
theorem f3EmptyMemsetGhostHook_eq
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyMemsetGhostHook keep P_sub entryTarget =
      memsetGhostHook keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget
    masterMemsetSpec hookMemset

/-- `f3EmptyMemsetGhostHookK` equals `memsetGhostHookK` specialized to `P_real := emptyStdProg`. -/
theorem f3EmptyMemsetGhostHookK_eq
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyMemsetGhostHookK keep P_sub entryTarget =
      memsetGhostHookK keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget
    (memsetSpecK keep masterMemsetSpec) hookMemset

/-! ## 3. State / Frame / `lr` Properties (`P_real` Hypotheses Discharged Unconditionally) -/

theorem f3EmptyMemsetGhostHook_fs
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyMemsetGhostHook keep P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keep emptyStdProg P_sub entryTarget _ hookMemset s0

theorem f3EmptyMemsetGhostHookK_fs
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyMemsetGhostHookK keep P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keep emptyStdProg P_sub entryTarget _ hookMemset s0

theorem f3EmptyMemsetGhostHook_fsT
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyMemsetGhostHook keep P_sub entryTarget) :=
  f3LinkedCallHook_fsT keep emptyStdProg P_sub entryTarget _ hookMemset

theorem f3EmptyMemsetGhostHookK_fsT
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyMemsetGhostHookK keep P_sub entryTarget) :=
  f3LinkedCallHook_fsT keep emptyStdProg P_sub entryTarget _ hookMemset

theorem f3EmptyMemsetGhostHook_trace
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    (f3EmptyMemsetGhostHook keep P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_trace rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemsetGhostHookK_trace
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    (f3EmptyMemsetGhostHookK keep P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_trace rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemsetGhostHook_vmPreserved
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    VmPreserved s0 (f3EmptyMemsetGhostHook keep P_sub entryTarget s0) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemsetGhostHookK_vmPreserved
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    VmPreserved s0 (f3EmptyMemsetGhostHookK keep P_sub entryTarget s0) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemsetGhostHook_oomPoolPreserved
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    OomPreserved s0 (f3EmptyMemsetGhostHook keep P_sub entryTarget s0) ∧
    PoolPreserved s0 (f3EmptyMemsetGhostHook keep P_sub entryTarget s0) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_oomPoolPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

theorem f3EmptyMemsetGhostHookK_oomPoolPreserved
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    OomPreserved s0 (f3EmptyMemsetGhostHookK keep P_sub entryTarget s0) ∧
    PoolPreserved s0 (f3EmptyMemsetGhostHookK keep P_sub entryTarget s0) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_oomPoolPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

/-- Any non-`.Exception` evaluation of `f3EmptyMemsetGhostHookK` automatically implies
    `keep (u.readReg64 .lr) = false` (discharging `hlr_out` at every ghost call step). -/
theorem f3EmptyMemsetGhostHookK_keepLr_false_of_noException
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg,
      (f3EmptyMemsetGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  rw [f3EmptyMemsetGhostHookK_eq] at hnoex
  exact memsetGhostHookK_keepLr_false_of_noException hnoex

theorem f3EmptyMemsetGhostHook_of_keepLr_true
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {u : State}
    (hActPre : ActiveRealPre masterMemsetSpec u)
    (hlr_in : keep (u.readReg64 .lr) = true) :
    f3EmptyMemsetGhostHook keep P_sub entryTarget u = hookMemset u := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_of_keepLr_true hActPre hlr_in

theorem f3EmptyMemsetGhostHookK_of_keepLr_true
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {u : State}
    (hlr_in : keep (u.readReg64 .lr) = true) :
    f3EmptyMemsetGhostHookK keep P_sub entryTarget u =
      { u with status := .Exception "ghost-hook precondition violated" } := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_of_keepLr_true hlr_in

/-! ## 4. Consumer `HookOk` Forwarding (Plain & `memsetSpecK` Variants) -/

section HookOkForwarding

variable {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget memsetWordsSym)
include hsvc_sub hsub_no hwords

theorem f3EmptyMemsetGhostHook_master_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) masterMemsetSpec := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_master_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHookK_masterK_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep masterMemsetSpec) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_masterK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_libcMemset_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) (libcMemsetSpec stk) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_libcMemset_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_sessionMemset_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) (sessionMemsetSpec stk) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemset_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_cliMemset_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) memsetSpec := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_cliMemset_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_memsetRegion_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) memsetRegionSpec := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_memsetRegion_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_sessionMemsetRegion_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) sessionMemsetRegionSpec := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemsetRegion_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_session2MemsetExtern_ok (stk : Nat := 16384) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) (session2MemsetExternSpec stk) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_session2MemsetExtern_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_libcMemset_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) (libcMemsetSpec stk).keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_libcMemset_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_sessionMemset_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) (sessionMemsetSpec stk).keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemset_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_cliMemset_keepsFs_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) memsetSpec.keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_cliMemset_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_memsetRegion_keepsFs_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) memsetRegionSpec.keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_memsetRegion_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_sessionMemsetRegion_keepsFs_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) sessionMemsetRegionSpec.keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemsetRegion_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_session2MemsetExtern_keepsFs_ok (stk : Nat := 16384) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (session2MemsetExternSpec stk).keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_session2MemsetExtern_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    stk

theorem f3EmptyMemsetGhostHook_memsetRegion_withStack_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) (withStack memsetRegionSpec stk) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_memsetRegion_withStack_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_sessionMemsetRegion_withStack_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withStack sessionMemsetRegionSpec stk) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemsetRegion_withStack_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords stk

theorem f3EmptyMemsetGhostHook_libcMemset_budget_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withVmPreserved (libcMemsetSpec stk)) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_libcMemset_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_libcMemset_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withVmPreserved (libcMemsetSpec stk)).keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_libcMemset_budget_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    stk

theorem f3EmptyMemsetGhostHook_sessionMemsetBudget_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) (sessionMemsetBudgetSpec stk) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemsetBudget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_sessionMemsetBudget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (sessionMemsetBudgetSpec stk).keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemsetBudget_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    stk

theorem f3EmptyMemsetGhostHook_cliMemset_budget_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withVmPreserved memsetSpec) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_cliMemset_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_session2MemsetExtern_budget_ok (stk : Nat := 16384) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withVmPreserved (session2MemsetExternSpec stk)) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_session2MemsetExtern_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    stk

theorem f3EmptyMemsetGhostHook_session2MemsetExtern_budget_keepsFs_ok (stk : Nat := 16384) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withVmPreserved (session2MemsetExternSpec stk)).keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_session2MemsetExtern_budget_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords stk

theorem f3EmptyMemsetGhostHook_memsetRegion_budget_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withVmPreserved memsetRegionSpec) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_memsetRegion_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_memsetRegion_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withStack (withVmPreserved memsetRegionSpec) stk) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_memsetRegion_budget_withStack_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords stk

theorem f3EmptyMemsetGhostHook_memsetRegion_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_memsetRegion_budget_withStack_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl)
    hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_sessionMemsetRegionBudget_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) sessionMemsetRegionBudgetSpec := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemsetRegionBudget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_sessionMemsetRegionBudget_withStack_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withStack sessionMemsetRegionBudgetSpec stk) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemsetRegionBudget_withStack_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords stk

theorem f3EmptyMemsetGhostHook_sessionMemsetRegionBudget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withStack sessionMemsetRegionBudgetSpec stk).keepsFs := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemsetRegionBudget_withStack_keepsFs_ok rfl hsvc_sub
    (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_memsetRegionCli_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) memsetRegionCliSpec := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_memsetRegionCli_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_libcMemsetCli_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) (libcMemsetCliSpec stk) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_libcMemsetCli_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_libcMemset_execFrozen_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withExecFrozen (libcMemsetSpec stk)) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_libcMemset_execFrozen_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_sessionMemset_execFrozen_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withExecFrozen (sessionMemsetSpec stk)) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemset_execFrozen_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHook_memsetRegion_execFrozen_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withExecFrozen memsetRegionSpec) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_memsetRegion_execFrozen_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHook_sessionMemsetRegion_execFrozen_ok :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withExecFrozen sessionMemsetRegionSpec) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_sessionMemsetRegion_execFrozen_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords

theorem f3EmptyMemsetGhostHook_session2MemsetExtern_execFrozen_ok (stk : Nat := 16384) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget)
      (withExecFrozen (session2MemsetExternSpec stk)) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_session2MemsetExtern_execFrozen_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords stk

omit hsvc_sub hsub_no hwords in
/-- Any plain `HookOk` on `f3EmptyMemsetGhostHook` also satisfies `memsetSpecK keep spec` (`rfl`-equal
    to `h2k_withKeepLrFalse keep spec`). -/
theorem f3EmptyMemsetGhostHook_any_memsetSpecK_ok {α : Type} {spec : Spec α}
    (hok : HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) spec) :
    HookOk (f3EmptyMemsetGhostHook keep P_sub entryTarget) (memsetSpecK keep spec) := by
  rw [f3EmptyMemsetGhostHook_eq] at hok ⊢
  exact memsetGhostHook_any_memsetSpecK_ok hok

theorem f3EmptyMemsetGhostHookK_libcMemsetK_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (libcMemsetSpec stk)) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_libcMemsetK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_sessionMemsetK_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (sessionMemsetSpec stk)) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_sessionMemsetK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_cliMemsetK_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep memsetSpec) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_cliMemsetK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHookK_memsetRegionK_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep memsetRegionSpec) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_memsetRegionK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHookK_sessionMemsetRegionK_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep sessionMemsetRegionSpec) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_sessionMemsetRegionK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHookK_libcMemsetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (libcMemsetSpec stk).keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_libcMemsetK_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_sessionMemsetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (sessionMemsetSpec stk).keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_sessionMemsetK_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_cliMemsetK_keepsFs_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep memsetSpec.keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_cliMemsetK_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHookK_memsetRegionK_keepsFs_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep memsetRegionSpec.keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_memsetRegionK_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHookK_sessionMemsetRegionK_keepsFs_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep sessionMemsetRegionSpec.keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_sessionMemsetRegionK_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords

theorem f3EmptyMemsetGhostHookK_libcMemsetK_budget_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved (libcMemsetSpec stk))) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_libcMemsetK_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_libcMemsetK_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved (libcMemsetSpec stk)).keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_libcMemsetK_budget_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    stk

theorem f3EmptyMemsetGhostHookK_sessionMemsetBudgetK_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (sessionMemsetBudgetSpec stk)) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_sessionMemsetBudgetK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_sessionMemsetBudgetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (sessionMemsetBudgetSpec stk).keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_sessionMemsetBudgetK_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords stk

theorem f3EmptyMemsetGhostHookK_cliMemsetK_budget_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved memsetSpec)) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_cliMemsetK_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHookK_memsetRegionK_budget_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved memsetRegionSpec)) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_memsetRegionK_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHookK_memsetRegionK_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (withStack (withVmPreserved memsetRegionSpec) stk)) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_memsetRegionK_budget_withStack_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords stk

theorem f3EmptyMemsetGhostHookK_memsetRegionK_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_memsetRegionK_budget_withStack_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl)
    hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_sessionMemsetRegionBudgetK_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep sessionMemsetRegionBudgetSpec) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_sessionMemsetRegionBudgetK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHookK_sessionMemsetRegionBudgetK_withStack_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (withStack sessionMemsetRegionBudgetSpec stk)) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_sessionMemsetRegionBudgetK_withStack_ok rfl hsvc_sub (fun _ _ => rfl)
    hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_sessionMemsetRegionBudgetK_withStack_keepsFs_ok
    (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (withStack sessionMemsetRegionBudgetSpec stk).keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_sessionMemsetRegionBudgetK_withStack_keepsFs_ok rfl hsvc_sub
    (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_memsetRegionCliK_ok :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep memsetRegionCliSpec) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_memsetRegionCliK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3EmptyMemsetGhostHookK_libcMemsetCliK_ok (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (libcMemsetCliSpec stk)) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_libcMemsetCliK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_session2MemsetExternK_ok (stk : Nat := 16384) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (session2MemsetExternSpec stk)) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_session2MemsetExternK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords stk

theorem f3EmptyMemsetGhostHookK_session2MemsetExternK_keepsFs_ok (stk : Nat := 16384) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (session2MemsetExternSpec stk).keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_session2MemsetExternK_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords stk

theorem f3EmptyMemsetGhostHookK_session2MemsetExternK_budget_ok (stk : Nat := 16384) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved (session2MemsetExternSpec stk))) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_session2MemsetExternK_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no
    hwords stk

theorem f3EmptyMemsetGhostHookK_session2MemsetExternK_budget_keepsFs_ok (stk : Nat := 16384) :
    HookOk (f3EmptyMemsetGhostHookK keep P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved (session2MemsetExternSpec stk)).keepsFs) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_session2MemsetExternK_budget_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl)
    hsub_no hwords stk

end HookOkForwarding

/-! ## 5. `emptyStdProg` First-Stop Witness & `emptyStdProg → P_real` Guarded Replays -/

/-- `W`-independent `StepsUntil emptyStdProg (SubroutineStop u)` first-stop execution witness for
    `f3EmptyMemsetGhostHook`: ready to be fed into the empty-lift hypothesis (`hLift`). -/
theorem f3EmptyMemsetGhostHook_stepsUntil
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyMemsetGhostHook keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget)
        (f3EmptyMemsetGhostHook keep P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyMemsetGhostHook keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemsetGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyMemsetGhostHook keep P_sub entryTarget u).fs = u.fs := by
  classical
  have hActPre : ActiveF3CallPre (fun _ _ => masterMemsetSpec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3EmptyMemsetGhostHook f3LinkedCallHook
    simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ := (activeF3CallPre_const_iff masterMemsetSpec u).mp hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS (P_real := emptyStdProg) rfl hsvc_sub (fun _ _ => rfl) hsub_no
      (subroutine_ok_masterMemset_of_hasWords hsub_no hwords)
      (specStripSInvariant_masterMemset keep)
      specPreservesFsTrace_masterMemset
      masterMemset_pre_setPC
      masterMemset_outcome_setPC
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  unfold f3EmptyMemsetGhostHook f3LinkedCallHook
  simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact ⟨hchoose.1, hchoose.2.1, hchoose.2.2.2.2, hchoose.2.2.1⟩

/-- `W`-independent `StepsUntil emptyStdProg (SubroutineStop u)` first-stop execution witness for
    `f3EmptyMemsetGhostHookK`, automatically discharging `keep (u.readReg64 .lr) = false` from
    `hnoex`. -/
theorem f3EmptyMemsetGhostHookK_stepsUntil
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyMemsetGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget)
        (f3EmptyMemsetGhostHookK keep P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyMemsetGhostHookK keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemsetGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyMemsetGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  classical
  have hlr_out : keep (u.readReg64 .lr) = false :=
    f3EmptyMemsetGhostHookK_keepLr_false_of_noException hnoex
  have hActPre : ActiveF3CallPre (fun _ _ => memsetSpecK keep masterMemsetSpec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3EmptyMemsetGhostHookK f3LinkedCallHook
    simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ :=
    (activeF3CallPre_const_iff (memsetSpecK keep masterMemsetSpec) u).mp hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS (P_real := emptyStdProg) rfl hsvc_sub (fun _ _ => rfl) hsub_no
      (subroutine_ok_masterMemsetK_of_hasWords keep hsub_no hwords)
      (specStripSInvariant_masterMemsetK keep)
      (specPreservesFsTrace_masterMemsetK keep)
      (masterMemsetK_pre_setPC keep)
      (masterMemsetK_outcome_setPC keep)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  unfold f3EmptyMemsetGhostHookK f3LinkedCallHook
  simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact ⟨hchoose.1, hchoose.2.1, hchoose.2.2.2.2, hchoose.2.2.1⟩

/-- **Memory-guarded `emptyStdProg → P_real` replay for `f3EmptyMemsetGhostHook`:**
    Bridges `f3EmptyMemsetGhostHook keep P_sub entryTarget` (`P_real := emptyStdProg`) to any real
    target program `P_real` (such as `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`) via
    `hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget` and the empty-lift hypothesis
    `hLift`. -/
theorem f3EmptyMemsetGhostHook_replayOn_of_emptyLift
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLift : ∀ (u sf : State),
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget) sf →
      SubroutineStop u sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemsetGhostHook keep P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (f3EmptyMemsetGhostHook keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemsetGhostHook keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyMemsetGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyMemsetGhostHook keep P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨huntil, hstop, hfr_sf, hfs_sf⟩ :=
    f3EmptyMemsetGhostHook_stepsUntil hsvc_sub hsub_no hwords hrun hnoex hfr hlr
      (hInvLoaded u.mem hfr hinv)
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  have hBodySteps : Steps P_real (u.setPC entryTarget)
      (f3EmptyMemsetGhostHook keep P_sub entryTarget u) :=
    hLift u _ hrun hfr hinv huntil hstop
  have hSteps : Steps P_real u (f3EmptyMemsetGhostHook keep P_sub entryTarget u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- **Memory-guarded `emptyStdProg → P_real` replay for `f3EmptyMemsetGhostHookK` (zero caller `lr`
    hypothesis!):**
    Discharges `keep (u.readReg64 .lr) = false` automatically from `hnoex` via
    `f3EmptyMemsetGhostHookK_keepLr_false_of_noException`. -/
theorem f3EmptyMemsetGhostHookK_replayOn_of_emptyLift
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLift : ∀ (u sf : State),
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget) sf →
      SubroutineStop u sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemsetGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (f3EmptyMemsetGhostHookK keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemsetGhostHookK keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyMemsetGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyMemsetGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨huntil, hstop, hfr_sf, hfs_sf⟩ :=
    f3EmptyMemsetGhostHookK_stepsUntil hsvc_sub hsub_no hwords hrun hnoex hfr
      (hInvLoaded u.mem hfr hinv)
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  have hBodySteps : Steps P_real (u.setPC entryTarget)
      (f3EmptyMemsetGhostHookK keep P_sub entryTarget u) :=
    hLift u _ hrun hfr hinv huntil hstop
  have hSteps : Steps P_real u (f3EmptyMemsetGhostHookK keep P_sub entryTarget u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Single-row `GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real` for
    `f3EmptyMemsetGhostHook keep P_sub entryTarget` via an `emptyStdProg → P_real` lift. -/
theorem f3EmptyMemsetGhostHook_replaysS_of_emptyLift
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemsetGhostHook keep P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLift : ∀ (u sf : State),
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget) sf →
      SubroutineStop u sf →
      Steps P_real (u.setPC entryTarget) sf) :
    GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyMemsetGhostHook_replayOn_of_emptyLift
    hsvc_sub hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf hLift
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-- Single-row `GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real` for
    `f3EmptyMemsetGhostHookK keep P_sub entryTarget` (polymorphic in `keep_any`). -/
theorem f3EmptyMemsetGhostHookK_replaysS_of_emptyLift
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemsetGhostHookK keep P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLift : ∀ (u sf : State),
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget) sf →
      SubroutineStop u sf →
      Steps P_real (u.setPC entryTarget) sf) :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyMemsetGhostHookK_replayOn_of_emptyLift
    hsvc_sub hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf hLift
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv
      ⟨hs, hfr', hinv'⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
