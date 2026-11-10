/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# `W`-Independent K-Convention `strlen` Ghost Hook & Stock-Safe `visitedIn` Replays (`HooksDehook.StrlenGhostK`)

Layout-independent, `CliElf`-free (`LibsignalBinary.Cli`-rootable) K-convention layer for the
placement-generic `strlen` ghost hook (`Card L2-b`):

1. **`strlenGhostHookK` Consumer `HookOk` Suite (All 11 SWAR-Padded Contracts + `withAlloc`):**
   Lifts `strlenGhostHookK_masterK_ok` across all 11 SWAR-padded `strlen` consumer specs (`_ok`,
   `_keepsFs_ok`, `_budget_ok`, `_budget_keepsFs_ok`, `_withAlloc_ok`, and `_withAllocK_ok`),
   including `hookOk_strlenSpecK_of_withAlloc` / `hookOk_withAlloc_of_strlenSpecK` commuting
   `strlenSpecK keep` with `WithAlloc.withAlloc`.
2. **`f3EmptyStrlenGhostHook` & `f3EmptyStrlenGhostHookK` (`P_real := emptyStdProg`):**
   Reuses `MemsetGhostK.emptyStdProg` (`Program.ofSvc Syscall.standard`, `rfl`-equal to
   `hole2_emptyProg`) and `MemsetGhostK.f3LinkedCallHook_const_eq_linkedCallHook` so the ghost hook
   has **zero dependence on `W : CliHooks`**, forwarding all `HookOk`, `HookFsTraced IsFsC`,
   `VmPreserved`, `OomPreserved ∧ PoolPreserved`, `ExecFrozen`, and `keep lr = false` lemmas with
   **zero `P_real` hypotheses**.
3. **Stock-Safe `h2fsgen_StepsVisitedIn`-Only Replay Bridges (`MUST` Rule):**
   Uses `h2fsgen_real_subroutine_run_visitedIn_of_stripS` and `h2fsgen_stepsUntil_det` to emit
   `h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) (f u)` (`_visitedIn`) and bridges
   across any `P_real` via a visited-PC lift premise `hLiftVis` (`_target_replay_of_visitedIn`,
   `_replayOn_of_visitedIn`, `_replaysS_of_visitedIn`) — with **zero** legacy `StepsUntil → Steps`
   `hLift` and **zero** `h2fsgen_HooksUnfetched`. Also exports direct `P_real` behind-stub replays
   `strlenGhostHook{,K}_replayOn`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostK

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (muslStrlenWords)
open CryptoVerification.SignalSession (strlenHook)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.Cli.MainHops (strlenSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (strlenSpecRO)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget
  VmPreserved OomPreserved PoolPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (
  cliStrlenPaddedSpec strlenPaddedSpecRO
  withStrlenPadRO withStrlenRoDataPad withStrlenAlignedEnd
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  ActiveF3CallPre f3LinkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_linkedCallHook ghostExternReplaysS_of_single_stub linkedCallHook_fs_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (memcpySpecK)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  activeF3CallPre_const_iff emptyStdProg f3LinkedCallHook_const_eq_linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode (
  masterStrlenSpec masterStrlenROSpec strlenSpecK
  subroutine_ok_masterStrlen_of_hasWords subroutine_ok_masterStrlenK_of_hasWords
  hookOk_cliStrlenPaddedK_of_master hookOk_strlenPaddedROK_of_master
  hookOk_strlenSpecRO_padROK_of_master hookOk_strlenSpecRO_roDataPadK_of_master
  hookOk_strlenSpecRO_alignedEndK_of_master
  hookOk_mainStrlen_padROK_of_master hookOk_mainStrlen_roDataPadK_of_master
  hookOk_mainStrlen_alignedEndK_of_master
  hookOk_cliExtStrlen_padROK_of_master hookOk_cliExtStrlen_roDataPadK_of_master
  hookOk_cliExtStrlen_alignedEndK_of_master
  strlenSpecK_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost (
  strlenByteLen strlenByteLen_eq
  strlenGhostHook strlenGhostHookK
  specStripSInvariant_masterStrlen specStripSInvariant_masterStrlenK
  specPreservesFsTrace_masterStrlen specPreservesFsTrace_masterStrlenK
  masterStrlen_pre_setPC masterStrlenK_pre_setPC
  masterStrlen_outcome_setPC masterStrlenK_outcome_setPC
  strlenGhostHook_master_ok strlenGhostHookK_masterK_ok
  strlenGhostHook_masterRO_ok strlenGhostHookK_masterROK_ok
  strlenGhostHook_masterVm_ok strlenGhostHookK_masterVmK_ok
  strlenGhostHook_fs strlenGhostHookK_fs
  strlenGhostHook_fsT strlenGhostHookK_fsT
  strlenGhostHook_vmPreserved strlenGhostHookK_vmPreserved
  strlenGhostHook_oomPoolPreserved strlenGhostHookK_oomPoolPreserved
  strlenGhostHook_trace strlenGhostHookK_trace
  strlenGhostHook_preserves_execFrozen strlenGhostHookK_preserves_execFrozen
  strlenGhostHookK_keepLr_false_of_noException
  strlenGhostHook_of_keepLr_true strlenGhostHookK_of_keepLr_true
  strlenGhostHookK_any_keepsFs_ok strlenGhostHook_any_strlenSpecK_ok
  strlenGhostHook_cliStrlenPadded_ok strlenGhostHook_cliStrlenPadded_keepsFs_ok
  strlenGhostHook_cliStrlenPadded_budget_ok strlenGhostHook_cliStrlenPadded_withAlloc_ok
  strlenGhostHook_strlenPaddedRO_ok strlenGhostHook_strlenPaddedRO_keepsFs_ok
  strlenGhostHook_strlenPaddedRO_budget_ok strlenGhostHook_strlenPaddedRO_withAlloc_ok
  strlenGhostHook_strlenSpecRO_padRO_ok strlenGhostHook_strlenSpecRO_padRO_budget_ok
  strlenGhostHook_strlenSpecRO_padRO_withAlloc_ok
  strlenGhostHook_mainStrlen_padRO_ok strlenGhostHook_mainStrlen_padRO_budget_ok
  strlenGhostHook_mainStrlen_padRO_withAlloc_ok
  strlenGhostHook_cliExtStrlen_padRO_ok strlenGhostHook_cliExtStrlen_padRO_budget_ok
  strlenGhostHook_cliExtStrlen_padRO_withAlloc_ok
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_real_subroutine_run_visitedIn_of_stripS h2fsgen_stepsUntil_det
)

/-! ## 1. `strlenSpecK` ↔ `withAlloc` Commutation & `strlenGhostHookK` Consumer Suite -/

theorem hookOk_strlenSpecK_of_withAlloc {α : Type} {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {f : State → State} {s0 : Spec α}
    (hh : HookOk f (withAlloc (M := M) A lim (strlenSpecK keep s0))) :
    HookOk f (strlenSpecK keep (withAlloc (M := M) A lim s0)) := by
  intro ⟨x, st⟩ R s hrun hpre hsp
  have hpre' : s.mem ⊨ (withAlloc (M := M) A lim (strlenSpecK keep s0)).pre (x, st) s ∗ R := by
    dsimp only [strlenSpecK, memcpySpecK, withAlloc] at hpre ⊢
    rw [sepConj_assoc ⌜keep (s.readReg64 .lr) = false⌝]
    exact hpre
  exact hh (x, st) R s hrun hpre' hsp

theorem hookOk_withAlloc_of_strlenSpecK {α : Type} {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {f : State → State} {s0 : Spec α}
    (hh : HookOk f (strlenSpecK keep (withAlloc (M := M) A lim s0))) :
    HookOk f (withAlloc (M := M) A lim (strlenSpecK keep s0)) := by
  intro ⟨x, st⟩ R s hrun hpre hsp
  have hpre' : s.mem ⊨ (strlenSpecK keep (withAlloc (M := M) A lim s0)).pre (x, st) s ∗ R := by
    dsimp only [strlenSpecK, memcpySpecK, withAlloc] at hpre ⊢
    rw [← sepConj_assoc ⌜keep (s.readReg64 .lr) = false⌝]
    exact hpre
  exact hh (x, st) R s hrun hpre' hsp

theorem hookOk_withAlloc_withVmPreserved_of_strlenSpecK {α : Type} {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {f : State → State} {spec : Spec α}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved spec))) :
    HookOk f (withAlloc (M := M) A lim (withVmPreserved (strlenSpecK keep spec))) := by
  have hh' : HookOk f (withVmPreserved (strlenSpecK keep spec)) := by
    rw [strlenSpecK_withVmPreserved]; exact hh
  exact hookOk_withAlloc_withVmPreserved A lim hh'

theorem hookOk_strlenSpecK_withAlloc_withVmPreserved {α : Type} {M : AllocCostModel}
    (keep : BitVec 64 → Bool) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {f : State → State} {spec : Spec α}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved spec))) :
    HookOk f (strlenSpecK keep (withAlloc (M := M) A lim (withVmPreserved spec))) := by
  have hw := hookOk_withAlloc_withVmPreserved_of_strlenSpecK keep A lim hh
  rw [strlenSpecK_withVmPreserved] at hw
  exact hookOk_strlenSpecK_of_withAlloc keep A lim hw

section KConsumerSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget muslStrlenWords)
variable (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)

include hsvc_real hsvc_sub hreal_no hsub_no hwords haddr

theorem strlenGhostHookK_any_withVmPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHookK keep P_real P_sub entryTarget) (strlenSpecK keep spec)) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved spec)) := by
  rw [← strlenSpecK_withVmPreserved]
  exact hookOk_withVmPreserved hh
    (strlenGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHookK_any_withAlloc_of_withVmPreserved_ok {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {spec : Spec α}
    (hh : HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved spec))) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withAlloc (M := M) A lim spec)) := by
  have hh' : HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (withVmPreserved (strlenSpecK keep spec)) := by
    rw [strlenSpecK_withVmPreserved]; exact hh
  exact hookOk_strlenSpecK_of_withAlloc keep A lim (hookOk_withAlloc_of_withVmPreserved A lim hh')

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHookK_any_withAlloc_withVmPreserved_ok {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {spec : Spec α}
    (hh : HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved spec))) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (strlenSpecK keep spec))) :=
  hookOk_withAlloc_withVmPreserved_of_strlenSpecK keep A lim hh

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHookK_any_strlenSpecK_withAlloc_ok {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {spec : Spec α}
    (hh : HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved spec))) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withAlloc (M := M) A lim (withVmPreserved spec))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim hh

-- All 11 SWAR-padded consumer contracts on `strlenGhostHookK`:
theorem strlenGhostHookK_cliStrlenPaddedK_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (cliStrlenPaddedSpec stk)) :=
  hookOk_cliStrlenPaddedK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHookK_cliStrlenPaddedK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (cliStrlenPaddedSpec stk).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_cliStrlenPaddedK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_cliStrlenPaddedK_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (cliStrlenPaddedSpec stk))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_cliStrlenPaddedK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_cliStrlenPaddedK_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (cliStrlenPaddedSpec stk)).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_cliStrlenPaddedK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_cliStrlenPaddedK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withAlloc (M := M) A lim (withVmPreserved (cliStrlenPaddedSpec stk)))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_cliStrlenPaddedK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHookK_strlenPaddedROK_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (strlenPaddedSpecRO stk)) :=
  hookOk_strlenPaddedROK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHookK_strlenPaddedROK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (strlenPaddedSpecRO stk).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_strlenPaddedROK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_strlenPaddedROK_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (strlenPaddedSpecRO stk))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_strlenPaddedROK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_strlenPaddedROK_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (strlenPaddedSpecRO stk)).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_strlenPaddedROK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_strlenPaddedROK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withAlloc (M := M) A lim (withVmPreserved (strlenPaddedSpecRO stk)))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_strlenPaddedROK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHookK_strlenSpecRO_padROK_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenPadRO (strlenSpecRO stk))) :=
  hookOk_strlenSpecRO_padROK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHookK_strlenSpecRO_padROK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenPadRO (strlenSpecRO stk)).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_strlenSpecRO_padROK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_strlenSpecRO_padROK_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (withStrlenPadRO (strlenSpecRO stk)))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_strlenSpecRO_padROK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_strlenSpecRO_padROK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withAlloc (M := M) A lim (withVmPreserved (withStrlenPadRO (strlenSpecRO stk))))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_strlenSpecRO_padROK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHookK_strlenSpecRO_roDataPadK_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenRoDataPad (strlenSpecRO stk))) :=
  hookOk_strlenSpecRO_roDataPadK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHookK_strlenSpecRO_roDataPadK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenRoDataPad (strlenSpecRO stk)).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_strlenSpecRO_roDataPadK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_strlenSpecRO_roDataPadK_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (withStrlenRoDataPad (strlenSpecRO stk)))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_strlenSpecRO_roDataPadK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_strlenSpecRO_roDataPadK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withAlloc (M := M) A lim (withVmPreserved (withStrlenRoDataPad (strlenSpecRO stk))))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_strlenSpecRO_roDataPadK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHookK_strlenSpecRO_alignedEndK_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenAlignedEnd (strlenSpecRO stk))) :=
  hookOk_strlenSpecRO_alignedEndK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHookK_strlenSpecRO_alignedEndK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenAlignedEnd (strlenSpecRO stk)).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_strlenSpecRO_alignedEndK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_strlenSpecRO_alignedEndK_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (withStrlenAlignedEnd (strlenSpecRO stk)))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_strlenSpecRO_alignedEndK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_strlenSpecRO_alignedEndK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withAlloc (M := M) A lim (withVmPreserved (withStrlenAlignedEnd (strlenSpecRO stk))))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_strlenSpecRO_alignedEndK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHookK_mainStrlen_padROK_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenPadRO (strlenSpec stk))) :=
  hookOk_mainStrlen_padROK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHookK_mainStrlen_padROK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenPadRO (strlenSpec stk)).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_mainStrlen_padROK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_mainStrlen_padROK_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (withStrlenPadRO (strlenSpec stk)))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_mainStrlen_padROK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_mainStrlen_padROK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withAlloc (M := M) A lim (withVmPreserved (withStrlenPadRO (strlenSpec stk))))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_mainStrlen_padROK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHookK_mainStrlen_roDataPadK_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenRoDataPad (strlenSpec stk))) :=
  hookOk_mainStrlen_roDataPadK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHookK_mainStrlen_roDataPadK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenRoDataPad (strlenSpec stk)).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_mainStrlen_roDataPadK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_mainStrlen_roDataPadK_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (withStrlenRoDataPad (strlenSpec stk)))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_mainStrlen_roDataPadK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_mainStrlen_roDataPadK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withAlloc (M := M) A lim (withVmPreserved (withStrlenRoDataPad (strlenSpec stk))))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_mainStrlen_roDataPadK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHookK_mainStrlen_alignedEndK_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenAlignedEnd (strlenSpec stk))) :=
  hookOk_mainStrlen_alignedEndK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHookK_mainStrlen_alignedEndK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenAlignedEnd (strlenSpec stk)).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_mainStrlen_alignedEndK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_mainStrlen_alignedEndK_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (withStrlenAlignedEnd (strlenSpec stk)))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_mainStrlen_alignedEndK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHookK_mainStrlen_alignedEndK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withAlloc (M := M) A lim (withVmPreserved (withStrlenAlignedEnd (strlenSpec stk))))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_mainStrlen_alignedEndK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHookK_cliExtStrlen_padROK_ok :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  hookOk_cliExtStrlen_padROK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHookK_cliExtStrlen_padROK_keepsFs_ok :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_cliExtStrlen_padROK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHookK_cliExtStrlen_padROK_budget_ok :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withVmPreserved (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_cliExtStrlen_padROK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHookK_cliExtStrlen_padROK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withAlloc (M := M) A lim
          (withVmPreserved
            (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec)))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_cliExtStrlen_padROK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

theorem strlenGhostHookK_cliExtStrlen_roDataPadK_ok :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  hookOk_cliExtStrlen_roDataPadK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHookK_cliExtStrlen_roDataPadK_keepsFs_ok :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_cliExtStrlen_roDataPadK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHookK_cliExtStrlen_roDataPadK_budget_ok :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withVmPreserved
          (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_cliExtStrlen_roDataPadK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHookK_cliExtStrlen_roDataPadK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withAlloc (M := M) A lim
          (withVmPreserved
            (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec)))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_cliExtStrlen_roDataPadK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

theorem strlenGhostHookK_cliExtStrlen_alignedEndK_ok :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  hookOk_cliExtStrlen_alignedEndK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHookK_cliExtStrlen_alignedEndK_keepsFs_ok :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec).keepsFs) :=
  strlenGhostHookK_any_keepsFs_ok
    (strlenGhostHookK_cliExtStrlen_alignedEndK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHookK_cliExtStrlen_alignedEndK_budget_ok :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withVmPreserved
          (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec))) :=
  strlenGhostHookK_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHookK_cliExtStrlen_alignedEndK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHookK_cliExtStrlen_alignedEndK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep
        (withAlloc (M := M) A lim
          (withVmPreserved
            (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec)))) :=
  hookOk_strlenSpecK_withAlloc_withVmPreserved keep A lim
    (strlenGhostHookK_cliExtStrlen_alignedEndK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

end KConsumerSuite

/-! ## 2. `W`-Independent `f3EmptyStrlenGhostHook{,K}` & `P_real`-Free Properties / `HookOk` -/

noncomputable def f3EmptyStrlenGhostHook
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => masterStrlenSpec) strlenHook
noncomputable def f3EmptyStrlenGhostHookK
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget
    (fun _ _ => strlenSpecK keep masterStrlenSpec) strlenHook
noncomputable abbrev f3EmptyStrlenGhostHookPure
    (keep : BitVec 64 → Bool) (entryTarget : BitVec 64) : State → State :=
  f3EmptyStrlenGhostHook keep (pureWordsProg entryTarget muslStrlenWords) entryTarget
noncomputable abbrev f3EmptyStrlenGhostHookPureK
    (keep : BitVec 64 → Bool) (entryTarget : BitVec 64) : State → State :=
  f3EmptyStrlenGhostHookK keep (pureWordsProg entryTarget muslStrlenWords) entryTarget

theorem f3EmptyStrlenGhostHook_eq
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyStrlenGhostHook keep P_sub entryTarget =
      strlenGhostHook keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget
    masterStrlenSpec strlenHook
theorem f3EmptyStrlenGhostHookK_eq
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyStrlenGhostHookK keep P_sub entryTarget =
      strlenGhostHookK keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget
    (strlenSpecK keep masterStrlenSpec) strlenHook

theorem f3EmptyStrlenGhostHook_fs
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyStrlenGhostHook keep P_sub entryTarget s0).fs = s0.fs := by
  rw [f3EmptyStrlenGhostHook_eq]; exact strlenGhostHook_fs keep emptyStdProg P_sub entryTarget s0
theorem f3EmptyStrlenGhostHookK_fs
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyStrlenGhostHookK keep P_sub entryTarget s0).fs = s0.fs := by
  rw [f3EmptyStrlenGhostHookK_eq]; exact strlenGhostHookK_fs keep emptyStdProg P_sub entryTarget s0
theorem f3EmptyStrlenGhostHook_fsT
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyStrlenGhostHook keep P_sub entryTarget) := by
  rw [f3EmptyStrlenGhostHook_eq]; exact strlenGhostHook_fsT keep emptyStdProg P_sub entryTarget
theorem f3EmptyStrlenGhostHookK_fsT
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyStrlenGhostHookK keep P_sub entryTarget) := by
  rw [f3EmptyStrlenGhostHookK_eq]; exact strlenGhostHookK_fsT keep emptyStdProg P_sub entryTarget
theorem f3EmptyStrlenGhostHook_preserves_execFrozen
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (f3EmptyStrlenGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHook keep P_sub entryTarget u).fs = u.fs := by
  rw [f3EmptyStrlenGhostHook_eq]
  exact strlenGhostHook_preserves_execFrozen keep emptyStdProg P_sub entryTarget hfr
theorem f3EmptyStrlenGhostHookK_preserves_execFrozen
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  rw [f3EmptyStrlenGhostHookK_eq]
  exact strlenGhostHookK_preserves_execFrozen keep emptyStdProg P_sub entryTarget hfr

theorem f3EmptyStrlenGhostHookK_keepLr_false_of_noException
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg, (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  rw [f3EmptyStrlenGhostHookK_eq] at hnoex; exact strlenGhostHookK_keepLr_false_of_noException hnoex

theorem f3EmptyStrlenGhostHook_of_keepLr_true
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hActPre : ActiveRealPre masterStrlenSpec s0) (hlr : keep (s0.readReg64 .lr) = true) :
    f3EmptyStrlenGhostHook keep P_sub entryTarget s0 = strlenHook s0 := by
  rw [f3EmptyStrlenGhostHook_eq]; exact strlenGhostHook_of_keepLr_true hActPre hlr

theorem f3EmptyStrlenGhostHookK_of_keepLr_true
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hlr : keep (s0.readReg64 .lr) = true) :
    f3EmptyStrlenGhostHookK keep P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  rw [f3EmptyStrlenGhostHookK_eq]; exact strlenGhostHookK_of_keepLr_true hlr

section F3EmptyHookOkForwarding

variable {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget muslStrlenWords)
variable (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)

include hsvc_sub hsub_no hwords haddr in
theorem f3EmptyStrlenGhostHook_trace (s0 : State) :
    (f3EmptyStrlenGhostHook keep P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyStrlenGhostHook_eq]
  exact strlenGhostHook_trace rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr s0
include hsvc_sub hsub_no hwords haddr in
theorem f3EmptyStrlenGhostHookK_trace (s0 : State) :
    (f3EmptyStrlenGhostHookK keep P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyStrlenGhostHookK_eq]
  exact strlenGhostHookK_trace rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr s0
include hsvc_sub hsub_no hwords haddr in
theorem f3EmptyStrlenGhostHook_vmPreserved (s0 : State) :
    VmPreserved s0 (f3EmptyStrlenGhostHook keep P_sub entryTarget s0) := by
  rw [f3EmptyStrlenGhostHook_eq]
  exact strlenGhostHook_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr s0
include hsvc_sub hsub_no hwords haddr in
theorem f3EmptyStrlenGhostHookK_vmPreserved (s0 : State) :
    VmPreserved s0 (f3EmptyStrlenGhostHookK keep P_sub entryTarget s0) := by
  rw [f3EmptyStrlenGhostHookK_eq]
  exact strlenGhostHookK_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr s0
include hsvc_sub hsub_no hwords haddr in
theorem f3EmptyStrlenGhostHook_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (f3EmptyStrlenGhostHook keep P_sub entryTarget s0) ∧
      PoolPreserved s0 (f3EmptyStrlenGhostHook keep P_sub entryTarget s0) := by
  rw [f3EmptyStrlenGhostHook_eq]
  exact strlenGhostHook_oomPoolPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr s0
include hsvc_sub hsub_no hwords haddr in
theorem f3EmptyStrlenGhostHookK_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (f3EmptyStrlenGhostHookK keep P_sub entryTarget s0) ∧
      PoolPreserved s0 (f3EmptyStrlenGhostHookK keep P_sub entryTarget s0) := by
  rw [f3EmptyStrlenGhostHookK_eq]
  exact strlenGhostHookK_oomPoolPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr s0

theorem f3EmptyStrlenGhostHook_ok_of_ghost {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHook keep emptyStdProg P_sub entryTarget) spec) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) spec := by
  rwa [f3EmptyStrlenGhostHook_eq]

theorem f3EmptyStrlenGhostHookK_ok_of_ghostK {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHookK keep emptyStdProg P_sub entryTarget) spec) :
    HookOk (f3EmptyStrlenGhostHookK keep P_sub entryTarget) spec := by
  rwa [f3EmptyStrlenGhostHookK_eq]

theorem f3EmptyStrlenGhostHook_any_strlenSpecK_ok {α : Type} {spec : Spec α}
    (hh : HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) spec) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) (strlenSpecK keep spec) := by
  rw [f3EmptyStrlenGhostHook_eq] at hh ⊢; exact strlenGhostHook_any_strlenSpecK_ok hh

include hsvc_sub hsub_no hwords haddr

theorem f3EmptyStrlenGhostHook_master_ok :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) masterStrlenSpec :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_master_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr)
theorem f3EmptyStrlenGhostHookK_masterK_ok :
    HookOk (f3EmptyStrlenGhostHookK keep P_sub entryTarget)
      (strlenSpecK keep masterStrlenSpec) :=
  f3EmptyStrlenGhostHookK_ok_of_ghostK
    (strlenGhostHookK_masterK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr)
theorem f3EmptyStrlenGhostHook_masterRO_ok :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) masterStrlenROSpec :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_masterRO_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr)
theorem f3EmptyStrlenGhostHookK_masterROK_ok :
    HookOk (f3EmptyStrlenGhostHookK keep P_sub entryTarget)
      (strlenSpecK keep masterStrlenROSpec) :=
  f3EmptyStrlenGhostHookK_ok_of_ghostK
    (strlenGhostHookK_masterROK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr)
theorem f3EmptyStrlenGhostHook_masterVm_ok :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) (withVmPreserved masterStrlenSpec) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_masterVm_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr)
theorem f3EmptyStrlenGhostHookK_masterVmK_ok :
    HookOk (f3EmptyStrlenGhostHookK keep P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved masterStrlenSpec)) :=
  f3EmptyStrlenGhostHookK_ok_of_ghostK
    (strlenGhostHookK_masterVmK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr)

-- Plain `f3EmptyStrlenGhostHook` consumer lifts (all 11 SWAR-padded contracts):
theorem f3EmptyStrlenGhostHook_cliStrlenPadded_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) (cliStrlenPaddedSpec stk) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_cliStrlenPadded_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHook_cliStrlenPadded_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) (cliStrlenPaddedSpec stk).keepsFs :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_cliStrlenPadded_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHook_cliStrlenPadded_budget_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withVmPreserved (cliStrlenPaddedSpec stk)) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_cliStrlenPadded_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHook_cliStrlenPadded_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (cliStrlenPaddedSpec stk))) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_cliStrlenPadded_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr A lim stk)

theorem f3EmptyStrlenGhostHook_strlenPaddedRO_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) (strlenPaddedSpecRO stk) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_strlenPaddedRO_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHook_strlenPaddedRO_keepsFs_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) (strlenPaddedSpecRO stk).keepsFs :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_strlenPaddedRO_keepsFs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHook_strlenPaddedRO_budget_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withVmPreserved (strlenPaddedSpecRO stk)) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_strlenPaddedRO_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHook_strlenPaddedRO_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (strlenPaddedSpecRO stk))) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_strlenPaddedRO_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr A lim stk)

theorem f3EmptyStrlenGhostHook_strlenSpecRO_padRO_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) (withStrlenPadRO (strlenSpecRO stk)) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_strlenSpecRO_padRO_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHook_strlenSpecRO_padRO_budget_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withVmPreserved (withStrlenPadRO (strlenSpecRO stk))) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_strlenSpecRO_padRO_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHook_strlenSpecRO_padRO_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStrlenPadRO (strlenSpecRO stk)))) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_strlenSpecRO_padRO_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr A lim stk)

theorem f3EmptyStrlenGhostHook_mainStrlen_padRO_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) (withStrlenPadRO (strlenSpec stk)) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_mainStrlen_padRO_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHook_mainStrlen_padRO_budget_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withVmPreserved (withStrlenPadRO (strlenSpec stk))) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_mainStrlen_padRO_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHook_mainStrlen_padRO_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStrlenPadRO (strlenSpec stk)))) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_mainStrlen_padRO_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr A lim stk)

theorem f3EmptyStrlenGhostHook_cliExtStrlen_padRO_ok :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_cliExtStrlen_padRO_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr)
theorem f3EmptyStrlenGhostHook_cliExtStrlen_padRO_budget_ok :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withVmPreserved (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_cliExtStrlen_padRO_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr)
theorem f3EmptyStrlenGhostHook_cliExtStrlen_padRO_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget)
      (withAlloc (M := M) A lim
        (withVmPreserved (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec))) :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_cliExtStrlen_padRO_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr A lim)

-- `K` `f3EmptyStrlenGhostHookK` headline consumer lifts (+ `f3EmptyStrlenGhostHookK_ok_of_ghostK` for all others):
theorem f3EmptyStrlenGhostHookK_cliStrlenPaddedK_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHookK keep P_sub entryTarget)
      (strlenSpecK keep (cliStrlenPaddedSpec stk)) :=
  f3EmptyStrlenGhostHookK_ok_of_ghostK
    (strlenGhostHookK_cliStrlenPaddedK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHookK_cliStrlenPaddedK_budget_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHookK keep P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (cliStrlenPaddedSpec stk))) :=
  f3EmptyStrlenGhostHookK_ok_of_ghostK
    (strlenGhostHookK_cliStrlenPaddedK_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHookK_cliStrlenPaddedK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHookK keep P_sub entryTarget)
      (strlenSpecK keep (withAlloc (M := M) A lim (withVmPreserved (cliStrlenPaddedSpec stk)))) :=
  f3EmptyStrlenGhostHookK_ok_of_ghostK
    (strlenGhostHookK_cliStrlenPaddedK_withAllocK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr A lim stk)

theorem f3EmptyStrlenGhostHookK_strlenPaddedROK_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHookK keep P_sub entryTarget)
      (strlenSpecK keep (strlenPaddedSpecRO stk)) :=
  f3EmptyStrlenGhostHookK_ok_of_ghostK
    (strlenGhostHookK_strlenPaddedROK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHookK_strlenPaddedROK_budget_ok (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHookK keep P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved (strlenPaddedSpecRO stk))) :=
  f3EmptyStrlenGhostHookK_ok_of_ghostK
    (strlenGhostHookK_strlenPaddedROK_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr stk)
theorem f3EmptyStrlenGhostHookK_strlenPaddedROK_withAllocK_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (f3EmptyStrlenGhostHookK keep P_sub entryTarget)
      (strlenSpecK keep (withAlloc (M := M) A lim (withVmPreserved (strlenPaddedSpecRO stk)))) :=
  f3EmptyStrlenGhostHookK_ok_of_ghostK
    (strlenGhostHookK_strlenPaddedROK_withAllocK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr A lim stk)

end F3EmptyHookOkForwarding

/-! ## 3. Stock-Safe `visitedIn`-Only Replay Bridges & Direct `P_real` Behind-Stub Replays -/

/-- `W`-independent `h2fsgen_StepsVisitedIn keep emptyStdProg` witness for
    `f3EmptyStrlenGhostHook`, pinning the `Classical.choose` endpoint via `h2fsgen_stepsUntil_det`. -/
theorem f3EmptyStrlenGhostHook_visitedIn
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyStrlenGhostHook keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget)
        (f3EmptyStrlenGhostHook keep P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyStrlenGhostHook keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyStrlenGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHook keep P_sub entryTarget u).fs = u.fs := by
  classical
  have hActPre : ActiveF3CallPre (fun _ _ => masterStrlenSpec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3EmptyStrlenGhostHook f3LinkedCallHook
    simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ := (activeF3CallPre_const_iff masterStrlenSpec u).mp hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS (P1 := emptyStdProg) rfl hsvc_sub
      (fun _ _ => rfl) hsub_no
      (subroutine_ok_masterStrlen_of_hasWords (entry := entryTarget) hsub_no hwords
        (by simpa [strlenByteLen_eq] using haddr))
      (specStripSInvariant_masterStrlen keep)
      specPreservesFsTrace_masterStrlen
      masterStrlen_pre_setPC
      masterStrlen_outcome_setPC
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : f3EmptyStrlenGhostHook keep P_sub entryTarget u = sf := by
    unfold f3EmptyStrlenGhostHook f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  rw [heq]
  exact ⟨hvis, hstop, hfr_sf, hfs⟩

/-- `W`-independent `h2fsgen_StepsVisitedIn keep emptyStdProg` witness for
    `f3EmptyStrlenGhostHookK`, automatically discharging `keep (u.readReg64 .lr) = false` from
    `hnoex` via `f3EmptyStrlenGhostHookK_keepLr_false_of_noException`. -/
theorem f3EmptyStrlenGhostHookK_visitedIn
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget)
        (f3EmptyStrlenGhostHookK keep P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyStrlenGhostHookK keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  classical
  have hlr_out : keep (u.readReg64 .lr) = false :=
    f3EmptyStrlenGhostHookK_keepLr_false_of_noException hnoex
  have hActPre : ActiveF3CallPre (fun _ _ => strlenSpecK keep masterStrlenSpec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3EmptyStrlenGhostHookK f3LinkedCallHook
    simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ :=
    (activeF3CallPre_const_iff (strlenSpecK keep masterStrlenSpec) u).mp hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS (P1 := emptyStdProg) rfl hsvc_sub
      (fun _ _ => rfl) hsub_no
      (subroutine_ok_masterStrlenK_of_hasWords keep (entry := entryTarget) hsub_no hwords
        (by simpa [strlenByteLen_eq] using haddr))
      (specStripSInvariant_masterStrlenK keep)
      (specPreservesFsTrace_masterStrlenK keep)
      (masterStrlenK_pre_setPC keep)
      (masterStrlenK_outcome_setPC keep)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : f3EmptyStrlenGhostHookK keep P_sub entryTarget u = sf := by
    unfold f3EmptyStrlenGhostHookK f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  rw [heq]
  exact ⟨hvis, hstop, hfr_sf, hfs⟩

theorem strlenGhostHook_empty_visitedIn
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (strlenGhostHook keep emptyStdProg P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget)
        (strlenGhostHook keep emptyStdProg P_sub entryTarget u) ∧
      SubroutineStop u (strlenGhostHook keep emptyStdProg P_sub entryTarget u) ∧
      ExecFrozen (strlenGhostHook keep emptyStdProg P_sub entryTarget u).mem ∧
      (strlenGhostHook keep emptyStdProg P_sub entryTarget u).fs = u.fs := by
  rw [← f3EmptyStrlenGhostHook_eq] at hnoex ⊢
  exact f3EmptyStrlenGhostHook_visitedIn hsvc_sub hsub_no hwords haddr hrun hnoex hFr hlr_out
    hCodeSub

theorem strlenGhostHookK_empty_visitedIn
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (strlenGhostHookK keep emptyStdProg P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget)
        (strlenGhostHookK keep emptyStdProg P_sub entryTarget u) ∧
      SubroutineStop u (strlenGhostHookK keep emptyStdProg P_sub entryTarget u) ∧
      ExecFrozen (strlenGhostHookK keep emptyStdProg P_sub entryTarget u).mem ∧
      (strlenGhostHookK keep emptyStdProg P_sub entryTarget u).fs = u.fs := by
  rw [← f3EmptyStrlenGhostHookK_eq] at hnoex ⊢
  exact f3EmptyStrlenGhostHookK_visitedIn hsvc_sub hsub_no hwords haddr hrun hnoex hFr hCodeSub

/-- Target-entry (`u.setPC entryTarget`) stock-safe replay for `f3EmptyStrlenGhostHook` via a
    visited-PC lift `hLiftVis`. -/
theorem f3EmptyStrlenGhostHook_target_replay_of_visitedIn
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLiftVis : ∀ (u sf : State),
      u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf)
    {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyStrlenGhostHook keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false) (hinv : InvMem u.mem) :
    Steps P_real (u.setPC entryTarget) (f3EmptyStrlenGhostHook keep P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyStrlenGhostHook keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyStrlenGhostHook keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyStrlenGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHook keep P_sub entryTarget u).fs = u.fs := by
  obtain ⟨hvis, hstop, hfr_sf, hfs_sf⟩ :=
    f3EmptyStrlenGhostHook_visitedIn hsvc_sub hsub_no hwords haddr hrun hnoex hFr hlr_out
      (hInvLoaded u.mem hFr hinv)
  have hBody := hLiftVis u _ hrun hFr hinv hvis
  exact ⟨hBody, hstop, hfr_sf, hInvKf u.mem _ hinv hBody.keepsFrozen, hfs_sf⟩

/-- Target-entry (`u.setPC entryTarget`) stock-safe replay for `f3EmptyStrlenGhostHookK` via
    `hLiftVis` (discharging `keep lr = false` automatically from `hnoex`). -/
theorem f3EmptyStrlenGhostHookK_target_replay_of_visitedIn
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLiftVis : ∀ (u sf : State),
      u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf)
    {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hinv : InvMem u.mem) :
    Steps P_real (u.setPC entryTarget) (f3EmptyStrlenGhostHookK keep P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyStrlenGhostHookK keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  obtain ⟨hvis, hstop, hfr_sf, hfs_sf⟩ :=
    f3EmptyStrlenGhostHookK_visitedIn hsvc_sub hsub_no hwords haddr hrun hnoex hFr
      (hInvLoaded u.mem hFr hinv)
  have hBody := hLiftVis u _ hrun hFr hinv hvis
  exact ⟨hBody, hstop, hfr_sf, hInvKf u.mem _ hinv hBody.keepsFrozen, hfs_sf⟩

/-- Behind-stub (`u.pc = stubPc`) stock-safe memory-guarded replay for `f3EmptyStrlenGhostHook` via
    `StubReachesTargetOn InvMem P_real stubPc entryTarget` and visited-PC lift `hLiftVis`. -/
theorem f3EmptyStrlenGhostHook_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLiftVis : ∀ (u sf : State),
      u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc → u.status = .Running →
      (∀ msg, (f3EmptyStrlenGhostHook keep P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (f3EmptyStrlenGhostHook keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyStrlenGhostHook keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyStrlenGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHook keep P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨hBody, _, hfr_sf, _, hfs_sf⟩ :=
    f3EmptyStrlenGhostHook_target_replay_of_visitedIn hsvc_sub hsub_no hwords haddr
      hInvLoaded hInvKf hLiftVis hrun hnoex hfr hlr hinv
  have hSteps := (hStub u hpc hrun hfr hinv).trans hBody
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Behind-stub (`u.pc = stubPc`) stock-safe memory-guarded replay for `f3EmptyStrlenGhostHookK` via
    `StubReachesTargetOn` and `hLiftVis` (zero caller `lr` premise). -/
theorem f3EmptyStrlenGhostHookK_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLiftVis : ∀ (u sf : State),
      u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc → u.status = .Running →
      (∀ msg, (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (f3EmptyStrlenGhostHookK keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨hBody, _, hfr_sf, _, hfs_sf⟩ :=
    f3EmptyStrlenGhostHookK_target_replay_of_visitedIn hsvc_sub hsub_no hwords haddr
      hInvLoaded hInvKf hLiftVis hrun hnoex hfr hinv
  have hSteps := (hStub u hpc hrun hfr hinv).trans hBody
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Single-stub `GhostExternReplaysS` for `f3EmptyStrlenGhostHook` via `hLiftVis`. -/
theorem f3EmptyStrlenGhostHook_replaysS_of_visitedIn
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyStrlenGhostHook keep P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLiftVis : ∀ (u sf : State),
      u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyStrlenGhostHook_replayOn_of_visitedIn
    hsvc_sub hsub_no hwords haddr hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-- Single-stub `GhostExternReplaysS keep_any` for `f3EmptyStrlenGhostHookK` via `hLiftVis`. -/
theorem f3EmptyStrlenGhostHookK_replaysS_of_visitedIn
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyStrlenGhostHookK keep P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLiftVis : ∀ (u sf : State),
      u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyStrlenGhostHookK_replayOn_of_visitedIn
    hsvc_sub hsub_no hwords haddr hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-- Direct `P_real` behind-stub memory-guarded replay for `strlenGhostHook`
    (`LinkedCallHookOn.ghostExternReplaysOn_of_linkedCallHook`). -/
theorem strlenGhostHook_replayOn
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc → u.status = .Running →
      (∀ msg, (strlenGhostHook keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (strlenGhostHook keep P_real P_sub entryTarget u) ∧
      ExecFrozen (strlenGhostHook keep P_real P_sub entryTarget u).mem ∧
      InvMem (strlenGhostHook keep P_real P_sub entryTarget u).mem ∧
      (strlenGhostHook keep P_real P_sub entryTarget u).fs = u.fs := by
  have hRep := ghostExternReplaysOn_of_linkedCallHook (fallback := strlenHook)
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf
    (subroutine_ok_masterStrlen_of_hasWords (entry := entryTarget) hsub_no hwords
      (by simpa [strlenByteLen_eq] using haddr))
    (specStripSInvariant_masterStrlen keep)
    specPreservesFsTrace_masterStrlen
    masterStrlen_pre_setPC
    masterStrlen_outcome_setPC
  refine ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨hs, hfr', hinv'⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
  exact ⟨hs, hfr', hinv', linkedCallHook_fs_eq u⟩

/-- Direct `P_real` behind-stub memory-guarded replay for `strlenGhostHookK` (zero caller `lr`
    premise, discharging `keep lr = false` from `hnoex`). -/
theorem strlenGhostHookK_replayOn
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc → u.status = .Running →
      (∀ msg, (strlenGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (strlenGhostHookK keep P_real P_sub entryTarget u) ∧
      ExecFrozen (strlenGhostHookK keep P_real P_sub entryTarget u).mem ∧
      InvMem (strlenGhostHookK keep P_real P_sub entryTarget u).mem ∧
      (strlenGhostHookK keep P_real P_sub entryTarget u).fs = u.fs := by
  have hRep := ghostExternReplaysOn_of_linkedCallHook (fallback := strlenHook)
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf
    (subroutine_ok_masterStrlenK_of_hasWords keep (entry := entryTarget) hsub_no hwords
      (by simpa [strlenByteLen_eq] using haddr))
    (specStripSInvariant_masterStrlenK keep)
    (specPreservesFsTrace_masterStrlenK keep)
    (masterStrlenK_pre_setPC keep)
    (masterStrlenK_outcome_setPC keep)
  refine ⟨hRep.1, fun u hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨hs, hfr', hinv'⟩ :=
    hRep.2 u hpc hrun hnoex hfr (strlenGhostHookK_keepLr_false_of_noException hnoex) hinv
  exact ⟨hs, hfr', hinv', linkedCallHook_fs_eq u⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostK
