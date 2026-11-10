/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhost -- proof-setup: allow-public-import

/-!
# Consumer `HookOk` Suite for Ghost `memrchr` Hooks (`HooksDehook.MemrchrGhostLifts`)

Card **R2-b** consumer `HookOk` lifts for `memrchrGhostFnLs` (**Route `β′`** `withLsRet`),
`memrchrGhostFn` (plain), and `memrchrGhostFnK` (`K`-narrowed), covering bounded-`stk`
(`∀ stk, 16 ≤ stk → stk ≤ 2 ^ 64 → …`) and `extHookStack` forms across `MainHops.memrchrSpec`,
`CalleesRO.memrchrSpecRO`, `Memrchr.cliMemrchrSpec`, and `CliExt.memrchrSpec`, together with
`keepsFs`, `withVmPreserved`, `withAlloc A lim`, `withOomPoolPreserved`, and `withExecFrozen`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostLifts

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved hookOk_withOomPoolPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Memrchr (cliMemrchrSpec)
open LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO (coreMemrchrWords)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (memrchrSpecRO)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  withLsRet withLsRet_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  withExecFrozen hookOk_withExecFrozen_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrCode (
  masterMemrchrSpec memrchrSpecK
  hookOk_memrchrSpecK_of_plain
  hookOk_mainHopsMemrchr_of_master hookOk_mainHopsMemrchrK_of_master
  hookOk_mainHopsMemrchrVm_of_master hookOk_mainHopsMemrchrVmK_of_master
  hookOk_cliMemrchr_of_master hookOk_cliMemrchrK_of_master
  hookOk_cliMemrchrVm_of_master hookOk_cliMemrchrVmK_of_master
  hookOk_cliExtMemrchr_of_master hookOk_cliExtMemrchrK_of_master
  hookOk_cliExtMemrchrVm_of_master hookOk_cliExtMemrchrVmK_of_master
  hookOk_cliExtMemrchr_keepsFs_of_master
  hookOk_memrchrRO_of_master hookOk_memrchrROK_of_master
  hookOk_memrchrROVm_of_master hookOk_memrchrROVmK_of_master
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhost (
  memrchrGhostFnLs memrchrGhostFn memrchrGhostFnK
  memrchrSpecK_withAlloc memrchrSpecK_withVmPreserved withLsRet_withAlloc
  memrchrGhostFnLs_fs memrchrGhostFn_fs memrchrGhostFnK_fs
  memrchrGhostFnLs_masterLs_ok memrchrGhostFn_master_ok memrchrGhostFnK_masterK_ok
  hookOk_withLsRet_of_memrchrSpecK
  memrchrGhostFnLs_vmPreserved memrchrGhostFn_vmPreserved memrchrGhostFnK_vmPreserved
  memrchrGhostFnLs_oomPoolPreserved memrchrGhostFn_oomPoolPreserved memrchrGhostFnK_oomPoolPreserved
  hookOk_withLsRet_mainHopsMemrchr_of_master hookOk_withLsRet_mainHopsMemrchrVm_of_master
  hookOk_withLsRet_cliMemrchr_of_master hookOk_withLsRet_cliMemrchrVm_of_master
  hookOk_withLsRet_cliExtMemrchr_of_master hookOk_withLsRet_cliExtMemrchrVm_of_master
  hookOk_withLsRet_cliExtMemrchr_keepsFs_of_master
  hookOk_withLsRet_memrchrRO_of_master hookOk_withLsRet_memrchrROVm_of_master
)

/-! ## 5. Complete Consumer `HookOk` Suite (Route `β′` `withLsRet`, Plain, `K`, & `withAlloc`) -/

section GenericHookOkSuite

variable {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entry coreMemrchrWords)

include hsvc_real hsvc_sub hreal_no hsub_no hwords

-- 5.1 Route `β′` (`withLsRet …`, C11 bounded-`stk` `∀ stk, 16 ≤ stk → stk ≤ 2 ^ 64 → …` + `extHookStack`):

theorem memrchrGhostFnLs_mainHopsMemrchr_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)) :=
  hookOk_withLsRet_mainHopsMemrchr_of_master
    (memrchrGhostFnLs_masterLs_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk hlo hhi

theorem memrchrGhostFnLs_mainHopsMemrchr_extHookStack_ok [LibsignalPlacement] :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack)) :=
  memrchrGhostFnLs_mainHopsMemrchr_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
    extHookStack (by decide) (by decide)

theorem memrchrGhostFnLs_mainHopsMemrchr_budget_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) :=
  hookOk_withLsRet_mainHopsMemrchrVm_of_master
    (memrchrGhostFnLs_masterLs_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFnLs_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords) stk hlo hhi

theorem memrchrGhostFnLs_mainHopsMemrchr_budget_extHookStack_ok [LibsignalPlacement] :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack))) :=
  memrchrGhostFnLs_mainHopsMemrchr_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
    extHookStack (by decide) (by decide)

theorem memrchrGhostFnLs_mainHopsMemrchr_withAlloc_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (withAlloc (M := M) A lim
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) := by
  rw [withLsRet_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (memrchrGhostFnLs_mainHopsMemrchr_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
      stk hlo hhi)

theorem memrchrGhostFnLs_mainHopsMemrchr_budget_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withAlloc (M := M) A lim (withLsRet (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)))) := by
  rw [withLsRet_withVmPreserved]
  exact hookOk_withAlloc_withVmPreserved A lim
    (withLsRet_withVmPreserved _ ▸
      memrchrGhostFnLs_mainHopsMemrchr_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
        stk hlo hhi)

theorem memrchrGhostFnLs_memrchrRO_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry) (withLsRet (memrchrSpecRO stk)) :=
  hookOk_withLsRet_memrchrRO_of_master
    (memrchrGhostFnLs_masterLs_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk hlo hhi

theorem memrchrGhostFnLs_memrchrRO_extHookStack_ok [LibsignalPlacement] :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry) (withLsRet (memrchrSpecRO extHookStack)) :=
  memrchrGhostFnLs_memrchrRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
    extHookStack (by decide) (by decide)

theorem memrchrGhostFnLs_memrchrRO_budget_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (withVmPreserved (memrchrSpecRO stk))) :=
  hookOk_withLsRet_memrchrROVm_of_master
    (memrchrGhostFnLs_masterLs_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFnLs_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords) stk hlo hhi

theorem memrchrGhostFnLs_memrchrRO_budget_extHookStack_ok [LibsignalPlacement] :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))) :=
  memrchrGhostFnLs_memrchrRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
    extHookStack (by decide) (by decide)

theorem memrchrGhostFnLs_memrchrRO_withAlloc_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (withAlloc (M := M) A lim (memrchrSpecRO stk))) := by
  rw [withLsRet_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (memrchrGhostFnLs_memrchrRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk hlo hhi)

theorem memrchrGhostFnLs_memrchrRO_budget_withAlloc_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withAlloc (M := M) A lim (withLsRet (withVmPreserved (memrchrSpecRO stk)))) := by
  rw [withLsRet_withVmPreserved]
  exact hookOk_withAlloc_withVmPreserved A lim
    (withLsRet_withVmPreserved _ ▸
      memrchrGhostFnLs_memrchrRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk hlo hhi)

theorem memrchrGhostFnLs_cliMemrchr_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry) (withLsRet (cliMemrchrSpec stk)) :=
  hookOk_withLsRet_cliMemrchr_of_master
    (memrchrGhostFnLs_masterLs_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk hlo hhi

theorem memrchrGhostFnLs_cliMemrchr_budget_ok [LibsignalPlacement]
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (withVmPreserved (cliMemrchrSpec stk))) :=
  hookOk_withLsRet_cliMemrchrVm_of_master
    (memrchrGhostFnLs_masterLs_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFnLs_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords) stk hlo hhi

theorem memrchrGhostFnLs_cliMemrchr_withAlloc_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (withAlloc (M := M) A lim (cliMemrchrSpec stk))) := by
  rw [withLsRet_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (memrchrGhostFnLs_cliMemrchr_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk hlo hhi)

theorem memrchrGhostFnLs_cliMemrchr_budget_withAlloc_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withAlloc (M := M) A lim (withLsRet (withVmPreserved (cliMemrchrSpec stk)))) := by
  rw [withLsRet_withVmPreserved]
  exact hookOk_withAlloc_withVmPreserved A lim
    (withLsRet_withVmPreserved _ ▸
      memrchrGhostFnLs_cliMemrchr_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk hlo hhi)

theorem memrchrGhostFnLs_cliExtMemrchr_ok [LibsignalPlacement] :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet CryptoVerification.SignalSession.CliExt.memrchrSpec) :=
  hookOk_withLsRet_cliExtMemrchr_of_master
    (memrchrGhostFnLs_masterLs_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memrchrGhostFnLs_cliExtMemrchr_keepsFs_ok [LibsignalPlacement] :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (keepsFs CryptoVerification.SignalSession.CliExt.memrchrSpec)) :=
  hookOk_withLsRet_cliExtMemrchr_keepsFs_of_master
    (memrchrGhostFnLs_masterLs_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memrchrGhostFnLs_cliExtMemrchr_budget_ok [LibsignalPlacement] :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec)) :=
  hookOk_withLsRet_cliExtMemrchrVm_of_master
    (memrchrGhostFnLs_masterLs_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFnLs_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memrchrGhostFnLs_cliExtMemrchr_withAlloc_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withLsRet (withAlloc (M := M) A lim CryptoVerification.SignalSession.CliExt.memrchrSpec)) := by
  rw [withLsRet_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (memrchrGhostFnLs_cliExtMemrchr_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memrchrGhostFnLs_cliExtMemrchr_budget_withAlloc_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry)
      (withAlloc (M := M) A lim
        (withLsRet (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec))) := by
  rw [withLsRet_withVmPreserved]
  exact hookOk_withAlloc_withVmPreserved A lim
    (withLsRet_withVmPreserved _ ▸
      memrchrGhostFnLs_cliExtMemrchr_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

-- 5.2 Plain contracts on `memrchrGhostFn` (`16 ≤ stk ≤ 2 ^ 64` + `extHookStack` + `withAlloc`):

theorem memrchrGhostFn_mainHopsMemrchr_ok (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry)
      (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk) :=
  hookOk_mainHopsMemrchr_of_master
    (memrchrGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFn_mainHopsMemrchr_budget_ok
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry)
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)) :=
  hookOk_mainHopsMemrchrVm_of_master
    (memrchrGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFn_mainHopsMemrchr_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry)
      (withAlloc (M := M) A lim
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (memrchrGhostFn_mainHopsMemrchr_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk hlo hhi)

theorem memrchrGhostFn_mainHopsMemrchr_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry)
      (withAlloc (M := M) A lim
        (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (memrchrGhostFn_mainHopsMemrchr_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk hlo hhi)

theorem memrchrGhostFn_memrchrRO_ok (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry) (memrchrSpecRO stk) :=
  hookOk_memrchrRO_of_master
    (memrchrGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFn_memrchrRO_budget_ok (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry) (withVmPreserved (memrchrSpecRO stk)) :=
  hookOk_memrchrROVm_of_master
    (memrchrGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFn_memrchrRO_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry)
      (withAlloc (M := M) A lim (memrchrSpecRO stk)) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (memrchrGhostFn_memrchrRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk hlo hhi)

theorem memrchrGhostFn_memrchrRO_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry)
      (withAlloc (M := M) A lim (withVmPreserved (memrchrSpecRO stk))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (memrchrGhostFn_memrchrRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk hlo hhi)

theorem memrchrGhostFn_cliMemrchr_ok (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry) (cliMemrchrSpec stk) :=
  hookOk_cliMemrchr_of_master
    (memrchrGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFn_cliMemrchr_budget_ok (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry) (withVmPreserved (cliMemrchrSpec stk)) :=
  hookOk_cliMemrchrVm_of_master
    (memrchrGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFn_cliExtMemrchr_ok :
    HookOk (memrchrGhostFn keepR P_real P_sub entry)
      CryptoVerification.SignalSession.CliExt.memrchrSpec :=
  hookOk_cliExtMemrchr_of_master
    (memrchrGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memrchrGhostFn_cliExtMemrchr_keepsFs_ok :
    HookOk (memrchrGhostFn keepR P_real P_sub entry)
      (keepsFs CryptoVerification.SignalSession.CliExt.memrchrSpec) :=
  hookOk_cliExtMemrchr_keepsFs_of_master
    (memrchrGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memrchrGhostFn_cliExtMemrchr_budget_ok :
    HookOk (memrchrGhostFn keepR P_real P_sub entry)
      (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec) :=
  hookOk_cliExtMemrchrVm_of_master
    (memrchrGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

-- 5.3 `K`-narrowed (`memrchrSpecK keepR …`) contracts on `memrchrGhostFnK` (+ `withLsRet` via `hKeep`):

theorem memrchrGhostFnK_masterLs_ok [LibsignalPlacement]
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry) (withLsRet masterMemrchrSpec) :=
  hookOk_withLsRet_of_memrchrSpecK hKeep
    (memrchrGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memrchrGhostFnK_mainHopsMemrchrK_ok (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry)
      (memrchrSpecK keepR (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)) :=
  hookOk_mainHopsMemrchrK_of_master keepR
    (memrchrGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFnK_mainHopsMemrchrK_budget_ok
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry)
      (memrchrSpecK keepR
        (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) :=
  hookOk_mainHopsMemrchrVmK_of_master keepR
    (memrchrGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFnK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFnK_mainHopsMemrchrK_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry)
      (memrchrSpecK keepR (withAlloc (M := M) A lim
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) := by
  rw [memrchrSpecK_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (memrchrGhostFnK_mainHopsMemrchrK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
      stk hlo hhi)

theorem memrchrGhostFnK_mainHopsMemrchrK_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry)
      (memrchrSpecK keepR (withAlloc (M := M) A lim
        (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)))) := by
  rw [memrchrSpecK_withAlloc, memrchrSpecK_withVmPreserved]
  exact hookOk_withAlloc_withVmPreserved A lim
    (memrchrSpecK_withVmPreserved keepR _ ▸
      memrchrGhostFnK_mainHopsMemrchrK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
        stk hlo hhi)

theorem memrchrGhostFnK_memrchrROK_ok (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry) (memrchrSpecK keepR (memrchrSpecRO stk)) :=
  hookOk_memrchrROK_of_master keepR
    (memrchrGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFnK_memrchrROK_budget_ok (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry)
      (memrchrSpecK keepR (withVmPreserved (memrchrSpecRO stk))) :=
  hookOk_memrchrROVmK_of_master keepR
    (memrchrGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFnK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFnK_memrchrROK_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry)
      (memrchrSpecK keepR (withAlloc (M := M) A lim (memrchrSpecRO stk))) := by
  rw [memrchrSpecK_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (memrchrGhostFnK_memrchrROK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk hlo hhi)

theorem memrchrGhostFnK_memrchrROK_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry)
      (memrchrSpecK keepR (withAlloc (M := M) A lim (withVmPreserved (memrchrSpecRO stk)))) := by
  rw [memrchrSpecK_withAlloc, memrchrSpecK_withVmPreserved]
  exact hookOk_withAlloc_withVmPreserved A lim
    (memrchrSpecK_withVmPreserved keepR _ ▸
      memrchrGhostFnK_memrchrROK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk hlo hhi)

theorem memrchrGhostFnK_cliMemrchrK_ok (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry) (memrchrSpecK keepR (cliMemrchrSpec stk)) :=
  hookOk_cliMemrchrK_of_master keepR
    (memrchrGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFnK_cliMemrchrK_budget_ok (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry)
      (memrchrSpecK keepR (withVmPreserved (cliMemrchrSpec stk))) :=
  hookOk_cliMemrchrVmK_of_master keepR
    (memrchrGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFnK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords) ⟨hlo, hhi⟩

theorem memrchrGhostFnK_cliExtMemrchrK_ok :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry)
      (memrchrSpecK keepR CryptoVerification.SignalSession.CliExt.memrchrSpec) :=
  hookOk_cliExtMemrchrK_of_master keepR
    (memrchrGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memrchrGhostFnK_cliExtMemrchrK_budget_ok :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry)
      (memrchrSpecK keepR (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec)) :=
  hookOk_cliExtMemrchrVmK_of_master keepR
    (memrchrGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memrchrGhostFnK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

-- 5.4 Generic `.keepsFs`, `withOomPoolPreserved`, `withExecFrozen`, & `memrchrSpecK` corollaries:

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memrchrGhostFnLs_any_keepsFs_ok [LibsignalPlacement] {α : Type} {spec : Spec α}
    (hh : HookOk (memrchrGhostFnLs keepR P_real P_sub entry) spec) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry) spec.keepsFs :=
  hh.keepsFs (memrchrGhostFnLs_fs keepR P_real P_sub entry)

theorem memrchrGhostFnLs_any_withOomPoolPreserved_ok [LibsignalPlacement] {α : Type} {spec : Spec α}
    (hh : HookOk (memrchrGhostFnLs keepR P_real P_sub entry) spec) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry) (withOomPoolPreserved spec) :=
  hookOk_withOomPoolPreserved hh
    (memrchrGhostFnLs_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memrchrGhostFnLs_any_execFrozen_ok [LibsignalPlacement] {α : Type} {spec : Spec α}
    (hh : HookOk (memrchrGhostFnLs keepR P_real P_sub entry) spec) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry) (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memrchrGhostFn_any_keepsFs_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memrchrGhostFn keepR P_real P_sub entry) spec) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry) spec.keepsFs :=
  hh.keepsFs (memrchrGhostFn_fs keepR P_real P_sub entry)

theorem memrchrGhostFn_any_withOomPoolPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memrchrGhostFn keepR P_real P_sub entry) spec) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry) (withOomPoolPreserved spec) :=
  hookOk_withOomPoolPreserved hh
    (memrchrGhostFn_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memrchrGhostFn_any_execFrozen_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memrchrGhostFn keepR P_real P_sub entry) spec) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry) (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memrchrGhostFn_any_memrchrSpecK_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memrchrGhostFn keepR P_real P_sub entry) spec) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry) (memrchrSpecK keepR spec) :=
  hookOk_memrchrSpecK_of_plain keepR hh

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memrchrGhostFnK_any_keepsFs_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memrchrGhostFnK keepR P_real P_sub entry) spec) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry) spec.keepsFs :=
  hh.keepsFs (memrchrGhostFnK_fs keepR P_real P_sub entry)

theorem memrchrGhostFnK_any_withOomPoolPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memrchrGhostFnK keepR P_real P_sub entry) spec) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry) (withOomPoolPreserved spec) :=
  hookOk_withOomPoolPreserved hh
    (memrchrGhostFnK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memrchrGhostFnK_any_execFrozen_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memrchrGhostFnK keepR P_real P_sub entry) spec) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry) (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

end GenericHookOkSuite

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostLifts
