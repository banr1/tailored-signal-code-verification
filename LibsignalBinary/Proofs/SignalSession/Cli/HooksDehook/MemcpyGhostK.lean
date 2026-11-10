/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost -- proof-setup: allow-public-import

/-!
# `K`-Narrowed `HookOk` Suite for `memcpyGhostHookK` (`HooksDehook.MemcpyGhostK`)

Companion module to `HooksDehook.MemcpyGhost` proving `HookOk (memcpyGhostHookK ...)` on
`memcpySpecK keep spec` (`⌜keep (s.readReg64 .lr) = false⌝ ∗ spec.pre`) for every `memcpy`
consumer contract on `main`, including `.keepsFs`, `withStack`, `withVmPreserved` / `*Budget`,
`SpqrV1.Alloc.ConcatBudgetAux` `Acp` (`AllocCallPreserved ∧ VmPreserved`), `allocMemcpyVmSpec`,
and `IfaceSimp` `OomPreserved ∧ PoolPreserved` variants.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostK

open Arm64 ProofLib SepProp
open VerifiedLibraries.Musl (memcpySymWords)
open CryptoVerification.LibsignalTripleRatchet (
  withStack
  sessionMemcpyRegionSpec sessionMemcpySpec framelessMemcpySpec memcpyROExtSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionMemcpyBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)
open CryptoVerification.SignalSession.CliExt (memcpySpec memcpyROSpec)
open CryptoVerification.SignalSession.Cli.MainHops (hookOk_withStack)
open LibsignalBinary.Heap (allocMemcpyVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (
  memcpyRegionCliSpec libcMemcpyCliSpec hookOk_withOomPoolPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  withExecFrozen hookOk_withExecFrozen_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  memcpySpecK
  hookOk_libcMemcpyK_of_master
  hookOk_sessionMemcpyK_of_master
  hookOk_cliMemcpyK_of_master
  hookOk_memcpyRegionK_of_master
  hookOk_sessionMemcpyRegionK_of_master
  hookOk_framelessMemcpyK_of_master
  hookOk_sessionMemcpyRegionROK_of_master
  hookOk_memcpyROExtK_of_master
  hookOk_cliMemcpyROK_of_master
  hookOk_sessionMemcpyRO4KK_of_master
  hookOk_framelessMemcpyBudgetFlatK_of_master
  hookOk_sessionMemcpyRO4KBudgetK_of_master
  hookOk_framelessMemcpyAcpK_of_master
  hookOk_sessionMemcpyRegionROAcpK_of_master
  hookOk_allocMemcpyVmK_of_master
  memcpySpecK_keepsFs memcpySpecK_withVmPreserved
  memcpySpecK_sessionMemcpyBudget memcpySpecK_sessionMemcpyRegionBudget
  memcpySpecK_framelessMemcpyBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  memcpyGhostHookK
  memcpyGhostHookK_masterK_ok memcpyGhostHookK_fs
  memcpyGhostHookK_vmPreserved memcpyGhostHookK_oomPoolPreserved memcpyGhostHookK_oracle
)

section GenericHookOkKSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget memcpySymWords)

include hsvc_real hsvc_sub hreal_no hsub_no hwords

theorem memcpyGhostHookK_libcMemcpyK_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (libcMemcpySpec stk)) :=
  hookOk_libcMemcpyK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHookK_sessionMemcpyK_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (sessionMemcpySpec stk)) :=
  hookOk_sessionMemcpyK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHookK_cliMemcpyK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget) (memcpySpecK keep memcpySpec) :=
  hookOk_cliMemcpyK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_memcpyRegionK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget) (memcpySpecK keep memcpyRegionSpec) :=
  hookOk_memcpyRegionK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyRegionK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep sessionMemcpyRegionSpec) :=
  hookOk_sessionMemcpyRegionK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_framelessMemcpyK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep framelessMemcpySpec) :=
  hookOk_framelessMemcpyK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyRegionROK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) :=
  hookOk_sessionMemcpyRegionROK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_memcpyROExtK_ok (stk : Nat := 16384) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (memcpyROExtSpec stk)) :=
  hookOk_memcpyROExtK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHookK_cliMemcpyROK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget) (memcpySpecK keep memcpyROSpec) :=
  hookOk_cliMemcpyROK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyRO4KK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K) :=
  hookOk_sessionMemcpyRO4KK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_libcMemcpyK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (libcMemcpySpec stk).keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_libcMemcpyK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_sessionMemcpyK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (sessionMemcpySpec stk).keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_sessionMemcpyK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_cliMemcpyK_keepsFs_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep memcpySpec.keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_cliMemcpyK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_memcpyRegionK_keepsFs_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep memcpyRegionSpec.keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_memcpyRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_sessionMemcpyRegionK_keepsFs_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep sessionMemcpyRegionSpec.keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_sessionMemcpyRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_framelessMemcpyK_keepsFs_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep framelessMemcpySpec.keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_framelessMemcpyK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_sessionMemcpyRegionROK_keepsFs_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec.keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_sessionMemcpyRegionROK_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_libcMemcpyK_budget_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved (libcMemcpySpec stk))) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_libcMemcpyK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_libcMemcpyK_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved (libcMemcpySpec stk)).keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_libcMemcpyK_budget_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_sessionMemcpyBudgetK_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (sessionMemcpyBudgetSpec stk)) := by
  rw [← memcpySpecK_sessionMemcpyBudget keep stk]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_sessionMemcpyK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyBudgetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (sessionMemcpyBudgetSpec stk).keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_sessionMemcpyBudgetK_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_cliMemcpyK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved memcpySpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_cliMemcpyK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_memcpyRegionK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved memcpyRegionSpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_memcpyRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_memcpyRegionK_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withStack (withVmPreserved memcpyRegionSpec) stk)) := by
  have hcomm : memcpySpecK keep (withStack (withVmPreserved memcpyRegionSpec) stk) =
      withStack (memcpySpecK keep (withVmPreserved memcpyRegionSpec)) stk := by
    unfold memcpySpecK withStack
    congr 1; funext x s; exact (sepConj_assoc _ _ _).symm
  rw [hcomm]
  exact hookOk_withStack
    (memcpyGhostHookK_memcpyRegionK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHookK_memcpyRegionK_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withStack (withVmPreserved memcpyRegionSpec) stk).keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_memcpyRegionK_budget_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_sessionMemcpyRegionBudgetK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep sessionMemcpyRegionBudgetSpec) := by
  rw [← memcpySpecK_sessionMemcpyRegionBudget]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_sessionMemcpyRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyRegionBudgetK_withStack_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withStack sessionMemcpyRegionBudgetSpec stk)) := by
  have hcomm : memcpySpecK keep (withStack sessionMemcpyRegionBudgetSpec stk) =
      withStack (memcpySpecK keep sessionMemcpyRegionBudgetSpec) stk := by
    unfold memcpySpecK withStack
    congr 1; funext x s; exact (sepConj_assoc _ _ _).symm
  rw [hcomm]
  exact hookOk_withStack
    (memcpyGhostHookK_sessionMemcpyRegionBudgetK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHookK_sessionMemcpyRegionBudgetK_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withStack sessionMemcpyRegionBudgetSpec stk).keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_sessionMemcpyRegionBudgetK_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_framelessMemcpyBudgetK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep framelessMemcpyBudgetSpec) := by
  rw [← memcpySpecK_framelessMemcpyBudget]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_framelessMemcpyK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_framelessMemcpyBudgetK_keepsFs_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep framelessMemcpyBudgetSpec.keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_framelessMemcpyBudgetK_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_framelessMemcpyBudgetFlatK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec) :=
  hookOk_framelessMemcpyBudgetFlatK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyRegionROK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep
        (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_sessionMemcpyRegionROK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyRegionROK_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep
        (withStack
          (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) stk)) := by
  have hcomm :
      memcpySpecK keep
        (withStack (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) stk) =
      withStack
        (memcpySpecK keep (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec))
        stk := by
    unfold memcpySpecK withStack
    congr 1; funext x s; exact (sepConj_assoc _ _ _).symm
  rw [hcomm]
  exact hookOk_withStack
    (memcpyGhostHookK_sessionMemcpyRegionROK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    stk

theorem memcpyGhostHookK_sessionMemcpyRegionROK_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep
        (withStack
          (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec)
          stk).keepsFs) := by
  rw [← memcpySpecK_keepsFs]
  exact (memcpyGhostHookK_sessionMemcpyRegionROK_budget_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHookK_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHookK_memcpyROExtK_budget_ok (stk : Nat := 16384) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved (memcpyROExtSpec stk))) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_memcpyROExtK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_cliMemcpyROK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved memcpyROSpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_cliMemcpyROK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyRO4KBudgetK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget.sessionMemcpyROSpec4K) :=
  hookOk_sessionMemcpyRO4KBudgetK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_framelessMemcpyAcpK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec) :=
  hookOk_framelessMemcpyAcpK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyRegionROAcpK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep
        LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec) :=
  hookOk_sessionMemcpyRegionROAcpK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_allocMemcpyVmK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep allocMemcpyVmSpec) :=
  hookOk_allocMemcpyVmK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_memcpyRegionCliK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep memcpyRegionCliSpec) :=
  hookOk_withOomPoolPreserved
    (memcpyGhostHookK_memcpyRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_libcMemcpyCliK_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (libcMemcpyCliSpec stk)) :=
  hookOk_withOomPoolPreserved
    (memcpyGhostHookK_libcMemcpyK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memcpyGhostHookK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memcpyGhostHookK_any_execFrozen_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memcpyGhostHookK keep P_real P_sub entryTarget) spec) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget) (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

end GenericHookOkKSuite

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostK
