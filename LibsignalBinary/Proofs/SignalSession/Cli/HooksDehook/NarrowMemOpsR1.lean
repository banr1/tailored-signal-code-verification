/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.MuslMemOpsRunsToPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import

/-!
# Layout-Free Narrow `memset` / `memcpy` Ghost-Hook R1 Witnesses (`HooksDehook.NarrowMemOpsR1`)

Provides layout-free, `W`-independent real-code narrow ghost hooks (`P_real := Program.ofSvc
Syscall.standard`) over `mallocngBlockProg mmpl 21 Syscall.standard` (`memset`) and
`mallocngBlockProg mmpl 20 Syscall.standard` (`memcpy`), sitting strictly below
`F3AllocStdinGhostHooks` and `ElfSlicesPqOomPlacedInst` (zero `F3*` or `Elf*` imports).

Closes H-REV Stage A Condition **C2** (`#1255`) at the `linkedCallHook` layer:
- unconditional `VmPreserved`, `.fs`, `.trace`, `ExecFrozen`, `HookNoAllocFailed`, and
  `HookFsTraced IsFsC` preservation across all three `linkedCallHook` branches;
- all R1 consumer `HookOk` lifts (`libcMem{set,cpy}Spec`, `sessionMem{set,cpy}Spec`,
  `{memset,memcpy}RegionSpec`, `sessionMem{set,cpy}RegionSpec`, `framelessMemcpySpec`,
  `SpqrV1.Alloc.sessionMemcpyRegionROSpec`);
- 1-term R1 conjunction & `∃ f, slot = some f ∧ ...` existential witnesses matching Stage A's
  `CliGhostAllocHooks` / `CliGhostSpqrAllocHooks` and `CliGhostA0Hooks` fields verbatim.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open CryptoVerification.LibsignalTripleRatchet (
  framelessMemcpySpec
  sessionMemcpyRegionSpec sessionMemcpySpec sessionMemsetRegionSpec sessionMemsetSpec
)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (
  HookNoAllocFailed hookNoAllocFailed_of_trace_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  mallocngBlockProg20_externAt_none mallocngBlockProg20_hasWords masterMemcpySpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  keepMemcpyBlk20
  memcpyGhostHook memcpyGhostHook_framelessMemcpy_ok memcpyGhostHook_fs
  memcpyGhostHook_fsT memcpyGhostHook_libcMemcpy_ok memcpyGhostHook_master_ok
  memcpyGhostHook_memcpyRegion_ok memcpyGhostHook_sessionMemcpyRegionRO_ok
  memcpyGhostHook_sessionMemcpyRegion_ok memcpyGhostHook_sessionMemcpy_ok
  memcpyGhostHook_trace memcpyGhostHook_vmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  mallocngBlockProg21_externAt_none mallocngBlockProg21_hasWords masterMemsetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  keepMemsetBlk21
  memsetGhostHook memsetGhostHook_fs memsetGhostHook_fsT
  memsetGhostHook_libcMemset_ok memsetGhostHook_master_ok
  memsetGhostHook_memsetRegion_ok memsetGhostHook_sessionMemsetRegion_ok
  memsetGhostHook_sessionMemset_ok memsetGhostHook_trace memsetGhostHook_vmPreserved
)

/-! ## 1. Layout-Free Narrow Ghost Hook Definitions -/

private theorem mallocngBlockProg_svc_eq (mmpl : MultiPlacement) (idx : Nat) :
    (mallocngBlockProg mmpl idx Syscall.standard).svc = Syscall.standard := rfl

private theorem stdProg_externAt_none (pc : BitVec 64) :
    (Program.ofSvc Syscall.standard).externAt? pc = none := rfl

/-- Layout-free `W`-independent narrow `memset` ghost hook (`P_real := Program.ofSvc Syscall.standard`,
    `P_sub := mallocngBlockProg mmpl 21 Syscall.standard`, `entryTarget := mmpl.base 21`). -/
@[expose] noncomputable def narrowMemsetGhostHook (mmpl : MultiPlacement) : State → State :=
  memsetGhostHook (keepMemsetBlk21 mmpl) (Program.ofSvc Syscall.standard)
    (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21)

/-- Layout-free `W`-independent narrow `memcpy` ghost hook (`P_real := Program.ofSvc Syscall.standard`,
    `P_sub := mallocngBlockProg mmpl 20 Syscall.standard`, `entryTarget := mmpl.base 20`). -/
@[expose] noncomputable def narrowMemcpyGhostHook (mmpl : MultiPlacement) : State → State :=
  memcpyGhostHook (keepMemcpyBlk20 mmpl) (Program.ofSvc Syscall.standard)
    (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20)

/-! ## 2. `narrowMemsetGhostHook` State-Frame & Consumer `HookOk` Lemmas -/

theorem narrowMemsetGhostHook_vmPreserved (mmpl : MultiPlacement) (s : State) :
    VmPreserved s (narrowMemsetGhostHook mmpl s) :=
  memsetGhostHook_vmPreserved rfl (mallocngBlockProg_svc_eq mmpl 21)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard) s

theorem narrowMemsetGhostHook_fs (mmpl : MultiPlacement) (s : State) :
    (narrowMemsetGhostHook mmpl s).fs = s.fs :=
  memsetGhostHook_fs (keepMemsetBlk21 mmpl) (Program.ofSvc Syscall.standard)
    (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21) s

theorem narrowMemsetGhostHook_fsT (mmpl : MultiPlacement) :
    HookFsTraced IsFsC (narrowMemsetGhostHook mmpl) :=
  memsetGhostHook_fsT (keepMemsetBlk21 mmpl) (Program.ofSvc Syscall.standard)
    (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21)

theorem narrowMemsetGhostHook_trace (mmpl : MultiPlacement) (s : State) :
    (narrowMemsetGhostHook mmpl s).trace = s.trace :=
  memsetGhostHook_trace rfl (mallocngBlockProg_svc_eq mmpl 21)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard) s

theorem narrowMemsetGhostHook_noAllocFailed (mmpl : MultiPlacement) :
    HookNoAllocFailed (narrowMemsetGhostHook mmpl) :=
  hookNoAllocFailed_of_trace_eq (narrowMemsetGhostHook mmpl) (narrowMemsetGhostHook_trace mmpl)

theorem narrowMemsetGhostHook_execFrozen (mmpl : MultiPlacement) (s : State)
    (hfr : ExecFrozen s.mem) :
    ExecFrozen (narrowMemsetGhostHook mmpl s).mem :=
  ExecFrozen.of_perm_eq hfr (narrowMemsetGhostHook_vmPreserved mmpl s).2.2.1

theorem narrowMemsetGhostHook_master_ok (mmpl : MultiPlacement) :
    HookOk (narrowMemsetGhostHook mmpl) masterMemsetSpec :=
  memsetGhostHook_master_ok rfl (mallocngBlockProg_svc_eq mmpl 21)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

theorem narrowMemsetGhostHook_libcMemset_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (narrowMemsetGhostHook mmpl) (libcMemsetSpec stk) :=
  memsetGhostHook_libcMemset_ok rfl (mallocngBlockProg_svc_eq mmpl 21)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard) stk

theorem narrowMemsetGhostHook_sessionMemset_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (narrowMemsetGhostHook mmpl) (sessionMemsetSpec stk) :=
  memsetGhostHook_sessionMemset_ok rfl (mallocngBlockProg_svc_eq mmpl 21)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard) stk

theorem narrowMemsetGhostHook_memsetRegion_ok (mmpl : MultiPlacement) :
    HookOk (narrowMemsetGhostHook mmpl) memsetRegionSpec :=
  memsetGhostHook_memsetRegion_ok rfl (mallocngBlockProg_svc_eq mmpl 21)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

theorem narrowMemsetGhostHook_sessionMemsetRegion_ok (mmpl : MultiPlacement) :
    HookOk (narrowMemsetGhostHook mmpl) sessionMemsetRegionSpec :=
  memsetGhostHook_sessionMemsetRegion_ok rfl (mallocngBlockProg_svc_eq mmpl 21)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

/-! ## 3. `narrowMemcpyGhostHook` State-Frame & Consumer `HookOk` Lemmas -/

theorem narrowMemcpyGhostHook_vmPreserved (mmpl : MultiPlacement) (s : State) :
    VmPreserved s (narrowMemcpyGhostHook mmpl s) :=
  memcpyGhostHook_vmPreserved rfl (mallocngBlockProg_svc_eq mmpl 20)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard) s

theorem narrowMemcpyGhostHook_fs (mmpl : MultiPlacement) (s : State) :
    (narrowMemcpyGhostHook mmpl s).fs = s.fs :=
  memcpyGhostHook_fs (keepMemcpyBlk20 mmpl) (Program.ofSvc Syscall.standard)
    (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20) s

theorem narrowMemcpyGhostHook_fsT (mmpl : MultiPlacement) :
    HookFsTraced IsFsC (narrowMemcpyGhostHook mmpl) :=
  memcpyGhostHook_fsT (keepMemcpyBlk20 mmpl) (Program.ofSvc Syscall.standard)
    (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20)

theorem narrowMemcpyGhostHook_trace (mmpl : MultiPlacement) (s : State) :
    (narrowMemcpyGhostHook mmpl s).trace = s.trace :=
  memcpyGhostHook_trace rfl (mallocngBlockProg_svc_eq mmpl 20)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard) s

theorem narrowMemcpyGhostHook_noAllocFailed (mmpl : MultiPlacement) :
    HookNoAllocFailed (narrowMemcpyGhostHook mmpl) :=
  hookNoAllocFailed_of_trace_eq (narrowMemcpyGhostHook mmpl) (narrowMemcpyGhostHook_trace mmpl)

theorem narrowMemcpyGhostHook_execFrozen (mmpl : MultiPlacement) (s : State)
    (hfr : ExecFrozen s.mem) :
    ExecFrozen (narrowMemcpyGhostHook mmpl s).mem :=
  ExecFrozen.of_perm_eq hfr (narrowMemcpyGhostHook_vmPreserved mmpl s).2.2.1

theorem narrowMemcpyGhostHook_master_ok (mmpl : MultiPlacement) :
    HookOk (narrowMemcpyGhostHook mmpl) masterMemcpySpec :=
  memcpyGhostHook_master_ok rfl (mallocngBlockProg_svc_eq mmpl 20)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

theorem narrowMemcpyGhostHook_libcMemcpy_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (narrowMemcpyGhostHook mmpl) (libcMemcpySpec stk) :=
  memcpyGhostHook_libcMemcpy_ok rfl (mallocngBlockProg_svc_eq mmpl 20)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard) stk

theorem narrowMemcpyGhostHook_sessionMemcpy_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (narrowMemcpyGhostHook mmpl) (sessionMemcpySpec stk) :=
  memcpyGhostHook_sessionMemcpy_ok rfl (mallocngBlockProg_svc_eq mmpl 20)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard) stk

theorem narrowMemcpyGhostHook_memcpyRegion_ok (mmpl : MultiPlacement) :
    HookOk (narrowMemcpyGhostHook mmpl) memcpyRegionSpec :=
  memcpyGhostHook_memcpyRegion_ok rfl (mallocngBlockProg_svc_eq mmpl 20)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

theorem narrowMemcpyGhostHook_sessionMemcpyRegion_ok (mmpl : MultiPlacement) :
    HookOk (narrowMemcpyGhostHook mmpl) sessionMemcpyRegionSpec :=
  memcpyGhostHook_sessionMemcpyRegion_ok rfl (mallocngBlockProg_svc_eq mmpl 20)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

theorem narrowMemcpyGhostHook_framelessMemcpy_ok (mmpl : MultiPlacement) :
    HookOk (narrowMemcpyGhostHook mmpl) framelessMemcpySpec :=
  memcpyGhostHook_framelessMemcpy_ok rfl (mallocngBlockProg_svc_eq mmpl 20)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

theorem narrowMemcpyGhostHook_sessionMemcpyRegionRO_ok (mmpl : MultiPlacement) :
    HookOk (narrowMemcpyGhostHook mmpl) sessionMemcpyRegionROSpec :=
  memcpyGhostHook_sessionMemcpyRegionRO_ok rfl (mallocngBlockProg_svc_eq mmpl 20)
    (fun pc _ => stdProg_externAt_none pc) (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

/-! ## 4. R1 Bundle Witnesses (Direct Conjunction + `∃ f, slot = some f ∧ ...` Existential) -/

/-- Direct R1 `memset` conjunction on `narrowMemsetGhostHook mmpl` (matches H-REV `rev_c10_c3.md`
    R-2 / T-1). -/
theorem narrowMemsetGhostHook_r1_conj (mmpl : MultiPlacement) :
    (∀ stk, 0 < stk → HookOk (narrowMemsetGhostHook mmpl) (libcMemsetSpec stk)) ∧
    (∀ stk, 0 < stk → HookOk (narrowMemsetGhostHook mmpl) (sessionMemsetSpec stk)) ∧
    HookOk (narrowMemsetGhostHook mmpl) memsetRegionSpec ∧
    HookOk (narrowMemsetGhostHook mmpl) sessionMemsetRegionSpec ∧
    (∀ s : State, VmPreserved s (narrowMemsetGhostHook mmpl s)) ∧
    (∀ s : State, (narrowMemsetGhostHook mmpl s).fs = s.fs) ∧
    HookFsTraced IsFsC (narrowMemsetGhostHook mmpl) :=
  ⟨fun stk _ => narrowMemsetGhostHook_libcMemset_ok mmpl stk,
   fun stk _ => narrowMemsetGhostHook_sessionMemset_ok mmpl stk,
   narrowMemsetGhostHook_memsetRegion_ok mmpl,
   narrowMemsetGhostHook_sessionMemsetRegion_ok mmpl,
   narrowMemsetGhostHook_vmPreserved mmpl,
   narrowMemsetGhostHook_fs mmpl,
   narrowMemsetGhostHook_fsT mmpl⟩

/-- Direct R1 `memcpy` conjunction on `narrowMemcpyGhostHook mmpl` (matches H-REV `rev_c10_c3.md`
    R-2 / T-1). -/
theorem narrowMemcpyGhostHook_r1_conj (mmpl : MultiPlacement) :
    (∀ stk, HookOk (narrowMemcpyGhostHook mmpl) (libcMemcpySpec stk)) ∧
    (∀ stk, HookOk (narrowMemcpyGhostHook mmpl) (sessionMemcpySpec stk)) ∧
    HookOk (narrowMemcpyGhostHook mmpl) memcpyRegionSpec ∧
    HookOk (narrowMemcpyGhostHook mmpl) sessionMemcpyRegionSpec ∧
    HookOk (narrowMemcpyGhostHook mmpl) framelessMemcpySpec ∧
    HookOk (narrowMemcpyGhostHook mmpl) sessionMemcpyRegionROSpec ∧
    (∀ s : State, VmPreserved s (narrowMemcpyGhostHook mmpl s)) ∧
    (∀ s : State, (narrowMemcpyGhostHook mmpl s).fs = s.fs) ∧
    HookFsTraced IsFsC (narrowMemcpyGhostHook mmpl) :=
  ⟨fun stk => narrowMemcpyGhostHook_libcMemcpy_ok mmpl stk,
   fun stk => narrowMemcpyGhostHook_sessionMemcpy_ok mmpl stk,
   narrowMemcpyGhostHook_memcpyRegion_ok mmpl,
   narrowMemcpyGhostHook_sessionMemcpyRegion_ok mmpl,
   narrowMemcpyGhostHook_framelessMemcpy_ok mmpl,
   narrowMemcpyGhostHook_sessionMemcpyRegionRO_ok mmpl,
   narrowMemcpyGhostHook_vmPreserved mmpl,
   narrowMemcpyGhostHook_fs mmpl,
   narrowMemcpyGhostHook_fsT mmpl⟩

/-- Exact 1-term existential witness for Stage A `CliGhostAllocHooks.memset` /
    `CliGhostSpqrAllocHooks.memset`. -/
theorem narrowMemsetGhostHook_r1_allocWitness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (narrowMemsetGhostHook mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f :=
  ⟨narrowMemsetGhostHook mmpl, hslot, narrowMemsetGhostHook_r1_conj mmpl⟩

/-- Exact 1-term existential witness for Stage A `CliGhostAllocHooks.memcpy` /
    `CliGhostSpqrAllocHooks.memcpy`. -/
theorem narrowMemcpyGhostHook_r1_allocWitness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (narrowMemcpyGhostHook mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f sessionMemcpyRegionROSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f :=
  ⟨narrowMemcpyGhostHook mmpl, hslot, narrowMemcpyGhostHook_r1_conj mmpl⟩

/-- Exact 1-term existential witness for Stage A `CliGhostA0Hooks.memset` (non-budget). -/
theorem narrowMemsetGhostHook_r1_a0Witness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (narrowMemsetGhostHook mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f :=
  ⟨narrowMemsetGhostHook mmpl, hslot,
   fun stk _ => narrowMemsetGhostHook_libcMemset_ok mmpl stk,
   fun stk _ => narrowMemsetGhostHook_sessionMemset_ok mmpl stk,
   narrowMemsetGhostHook_memsetRegion_ok mmpl,
   narrowMemsetGhostHook_sessionMemsetRegion_ok mmpl,
   narrowMemsetGhostHook_fs mmpl,
   narrowMemsetGhostHook_fsT mmpl⟩

/-- Exact 1-term existential witness for Stage A `CliGhostA0Hooks.memcpy` (non-budget). -/
theorem narrowMemcpyGhostHook_r1_a0Witness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (narrowMemcpyGhostHook mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f sessionMemcpyRegionROSpec ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f :=
  ⟨narrowMemcpyGhostHook mmpl, hslot,
   fun stk => narrowMemcpyGhostHook_libcMemcpy_ok mmpl stk,
   fun stk => narrowMemcpyGhostHook_sessionMemcpy_ok mmpl stk,
   narrowMemcpyGhostHook_memcpyRegion_ok mmpl,
   narrowMemcpyGhostHook_sessionMemcpyRegion_ok mmpl,
   narrowMemcpyGhostHook_framelessMemcpy_ok mmpl,
   narrowMemcpyGhostHook_sessionMemcpyRegionRO_ok mmpl,
   narrowMemcpyGhostHook_fs mmpl,
   narrowMemcpyGhostHook_fsT mmpl⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1
