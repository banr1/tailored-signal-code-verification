/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1 -- proof-setup: allow-public-import

/-!
# `f3LinkedCallHook` Narrow `rfl` Twins & R1 Witnesses (`HooksDehook.NarrowF3R1Witness`)

Defines `f3EmptyMemsetGhostHookNarrow mmpl` and `f3EmptyMemcpyGhostHookNarrow mmpl` via
`f3EmptyMemsetGhostHook` / `f3EmptyMemcpyGhostHook` (`P_real := emptyStdProg = Program.ofSvc
Syscall.standard`), sitting **strictly below** `ElfSlicesPqOomPlacedInst`, `CliF3MainOkBridge`,
and `ElfSlicesPqOomH2KHooks` (`0` `Elf*` / `PlacedInst` / `CliF3MainOkBridge` modules in its
import closure).

Because `ElfSlicesPqOomPlacedInst.hole2_emptyProg` is definitionally `Program.ofSvc
Syscall.standard = emptyStdProg`, these two definitions are **`rfl`-identical** to
`ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow mmpl` and
`ElfSlicesPqOomH2KMemcpy.h2k_memcpyGhostHookNarrow mmpl` (pinned by `rfl` in
`ElfSlicesPqOomH2KNarrowR1.lean`), breaking the `H2KMemset → PlacedInst` import cycle (`rev_c10_c3`
item 5) while satisfying `rev_c10_c3` R-6 (`hole2_ghFixed` and `h2k_ghFixedK` install `rfl`-equal
narrow terms).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness

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
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (HookNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  mallocngBlockProg20_externAt_none mallocngBlockProg20_hasWords masterMemcpySpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (keepMemcpyBlk20)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact (
  HookExactMemcpy f3EmptyMemcpyGhostHook_exact
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn (
  f3EmptyMemcpyGhostHook f3EmptyMemcpyGhostHook_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (masterMemsetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (keepMemsetBlk21)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  f3EmptyMemsetGhostHook f3EmptyMemsetGhostHook_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1 (
  narrowMemcpyGhostHook narrowMemcpyGhostHook_execFrozen
  narrowMemcpyGhostHook_framelessMemcpy_ok narrowMemcpyGhostHook_fs narrowMemcpyGhostHook_fsT
  narrowMemcpyGhostHook_libcMemcpy_ok narrowMemcpyGhostHook_master_ok
  narrowMemcpyGhostHook_memcpyRegion_ok narrowMemcpyGhostHook_noAllocFailed
  narrowMemcpyGhostHook_r1_a0Witness narrowMemcpyGhostHook_r1_allocWitness
  narrowMemcpyGhostHook_r1_conj narrowMemcpyGhostHook_sessionMemcpyRegionRO_ok
  narrowMemcpyGhostHook_sessionMemcpyRegion_ok narrowMemcpyGhostHook_sessionMemcpy_ok
  narrowMemcpyGhostHook_trace narrowMemcpyGhostHook_vmPreserved
  narrowMemsetGhostHook narrowMemsetGhostHook_execFrozen
  narrowMemsetGhostHook_fs narrowMemsetGhostHook_fsT narrowMemsetGhostHook_libcMemset_ok
  narrowMemsetGhostHook_master_ok narrowMemsetGhostHook_memsetRegion_ok
  narrowMemsetGhostHook_noAllocFailed narrowMemsetGhostHook_r1_a0Witness
  narrowMemsetGhostHook_r1_allocWitness narrowMemsetGhostHook_r1_conj
  narrowMemsetGhostHook_sessionMemsetRegion_ok narrowMemsetGhostHook_sessionMemset_ok
  narrowMemsetGhostHook_trace narrowMemsetGhostHook_vmPreserved
)

/-! ## 1. `f3LinkedCallHook` Narrow Twin Definitions & Bridge to `NarrowMemOpsR1` -/

private theorem mallocngBlockProg20_svc_eq (mmpl : MultiPlacement) :
    (mallocngBlockProg mmpl 20 Syscall.standard).svc = Syscall.standard := rfl

/-- `W`-independent `f3LinkedCallHook` narrow `memset` ghost hook (`rfl`-equal to
    `ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow mmpl`). Suitable for direct installation in
    `ElfSlicesPqOomPlacedInst.hole2_ghFixed` and `ElfSlicesPqOomH2KHooks.h2k_ghFixedK` without
    importing `ElfSlicesPqOomPlacedInst`. -/
@[expose] noncomputable def f3EmptyMemsetGhostHookNarrow (mmpl : MultiPlacement) : State → State :=
  f3EmptyMemsetGhostHook (keepMemsetBlk21 mmpl)
    (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21)

/-- `W`-independent `f3LinkedCallHook` narrow `memcpy` ghost hook (`rfl`-equal to
    `ElfSlicesPqOomH2KMemcpy.h2k_memcpyGhostHookNarrow mmpl`). Suitable for direct installation in
    `ElfSlicesPqOomPlacedInst.hole2_ghFixed` and `ElfSlicesPqOomH2KHooks.h2k_ghFixedK` without
    importing `ElfSlicesPqOomPlacedInst`. -/
@[expose] noncomputable def f3EmptyMemcpyGhostHookNarrow (mmpl : MultiPlacement) : State → State :=
  f3EmptyMemcpyGhostHook (keepMemcpyBlk20 mmpl)
    (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20)

theorem f3EmptyMemsetGhostHookNarrow_eq_narrow (mmpl : MultiPlacement) :
    f3EmptyMemsetGhostHookNarrow mmpl = narrowMemsetGhostHook mmpl :=
  f3EmptyMemsetGhostHook_eq (keepMemsetBlk21 mmpl)
    (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21)

theorem f3EmptyMemcpyGhostHookNarrow_eq_narrow (mmpl : MultiPlacement) :
    f3EmptyMemcpyGhostHookNarrow mmpl = narrowMemcpyGhostHook mmpl :=
  f3EmptyMemcpyGhostHook_eq (keepMemcpyBlk20 mmpl)
    (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20)

/-! ## 2. `f3EmptyMemsetGhostHookNarrow` State-Frame & Consumer `HookOk` Lemmas -/

theorem f3EmptyMemsetGhostHookNarrow_vmPreserved (mmpl : MultiPlacement) (s : State) :
    VmPreserved s (f3EmptyMemsetGhostHookNarrow mmpl s) := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_vmPreserved mmpl s

theorem f3EmptyMemsetGhostHookNarrow_fs (mmpl : MultiPlacement) (s : State) :
    (f3EmptyMemsetGhostHookNarrow mmpl s).fs = s.fs := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_fs mmpl s

theorem f3EmptyMemsetGhostHookNarrow_fsT (mmpl : MultiPlacement) :
    HookFsTraced IsFsC (f3EmptyMemsetGhostHookNarrow mmpl) := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_fsT mmpl

theorem f3EmptyMemsetGhostHookNarrow_trace (mmpl : MultiPlacement) (s : State) :
    (f3EmptyMemsetGhostHookNarrow mmpl s).trace = s.trace := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_trace mmpl s

theorem f3EmptyMemsetGhostHookNarrow_noAllocFailed (mmpl : MultiPlacement) :
    HookNoAllocFailed (f3EmptyMemsetGhostHookNarrow mmpl) := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_noAllocFailed mmpl

theorem f3EmptyMemsetGhostHookNarrow_execFrozen (mmpl : MultiPlacement) (s : State)
    (hfr : ExecFrozen s.mem) :
    ExecFrozen (f3EmptyMemsetGhostHookNarrow mmpl s).mem := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_execFrozen mmpl s hfr

theorem f3EmptyMemsetGhostHookNarrow_master_ok (mmpl : MultiPlacement) :
    HookOk (f3EmptyMemsetGhostHookNarrow mmpl) masterMemsetSpec := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_master_ok mmpl

theorem f3EmptyMemsetGhostHookNarrow_libcMemset_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookNarrow mmpl) (libcMemsetSpec stk) := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_libcMemset_ok mmpl stk

theorem f3EmptyMemsetGhostHookNarrow_sessionMemset_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (f3EmptyMemsetGhostHookNarrow mmpl) (sessionMemsetSpec stk) := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_sessionMemset_ok mmpl stk

theorem f3EmptyMemsetGhostHookNarrow_memsetRegion_ok (mmpl : MultiPlacement) :
    HookOk (f3EmptyMemsetGhostHookNarrow mmpl) memsetRegionSpec := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_memsetRegion_ok mmpl

theorem f3EmptyMemsetGhostHookNarrow_sessionMemsetRegion_ok (mmpl : MultiPlacement) :
    HookOk (f3EmptyMemsetGhostHookNarrow mmpl) sessionMemsetRegionSpec := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_sessionMemsetRegion_ok mmpl

/-! ## 3. `f3EmptyMemcpyGhostHookNarrow` State-Frame, `HookExactMemcpy`, & Consumer `HookOk` Lemmas -/

theorem f3EmptyMemcpyGhostHookNarrow_vmPreserved (mmpl : MultiPlacement) (s : State) :
    VmPreserved s (f3EmptyMemcpyGhostHookNarrow mmpl s) := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_vmPreserved mmpl s

theorem f3EmptyMemcpyGhostHookNarrow_fs (mmpl : MultiPlacement) (s : State) :
    (f3EmptyMemcpyGhostHookNarrow mmpl s).fs = s.fs := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_fs mmpl s

theorem f3EmptyMemcpyGhostHookNarrow_fsT (mmpl : MultiPlacement) :
    HookFsTraced IsFsC (f3EmptyMemcpyGhostHookNarrow mmpl) := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_fsT mmpl

theorem f3EmptyMemcpyGhostHookNarrow_trace (mmpl : MultiPlacement) (s : State) :
    (f3EmptyMemcpyGhostHookNarrow mmpl s).trace = s.trace := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_trace mmpl s

theorem f3EmptyMemcpyGhostHookNarrow_noAllocFailed (mmpl : MultiPlacement) :
    HookNoAllocFailed (f3EmptyMemcpyGhostHookNarrow mmpl) := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_noAllocFailed mmpl

theorem f3EmptyMemcpyGhostHookNarrow_execFrozen (mmpl : MultiPlacement) (s : State)
    (hfr : ExecFrozen s.mem) :
    ExecFrozen (f3EmptyMemcpyGhostHookNarrow mmpl s).mem := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_execFrozen mmpl s hfr

theorem f3EmptyMemcpyGhostHookNarrow_exact (mmpl : MultiPlacement) :
    HookExactMemcpy (f3EmptyMemcpyGhostHookNarrow mmpl) :=
  f3EmptyMemcpyGhostHook_exact (keepMemcpyBlk20 mmpl) (mallocngBlockProg20_svc_eq mmpl)
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

theorem f3EmptyMemcpyGhostHookNarrow_master_ok (mmpl : MultiPlacement) :
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) masterMemcpySpec := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_master_ok mmpl

theorem f3EmptyMemcpyGhostHookNarrow_libcMemcpy_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) (libcMemcpySpec stk) := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_libcMemcpy_ok mmpl stk

theorem f3EmptyMemcpyGhostHookNarrow_sessionMemcpy_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) (sessionMemcpySpec stk) := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_sessionMemcpy_ok mmpl stk

theorem f3EmptyMemcpyGhostHookNarrow_memcpyRegion_ok (mmpl : MultiPlacement) :
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) memcpyRegionSpec := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_memcpyRegion_ok mmpl

theorem f3EmptyMemcpyGhostHookNarrow_sessionMemcpyRegion_ok (mmpl : MultiPlacement) :
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) sessionMemcpyRegionSpec := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_sessionMemcpyRegion_ok mmpl

theorem f3EmptyMemcpyGhostHookNarrow_framelessMemcpy_ok (mmpl : MultiPlacement) :
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) framelessMemcpySpec := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_framelessMemcpy_ok mmpl

theorem f3EmptyMemcpyGhostHookNarrow_sessionMemcpyRegionRO_ok (mmpl : MultiPlacement) :
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) sessionMemcpyRegionROSpec := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_sessionMemcpyRegionRO_ok mmpl

/-! ## 4. R1 Bundle Witnesses (`_r1_conj`, `_r1_allocWitness`, `_r1_a0Witness`) -/

/-- Direct R1 `memset` conjunction on `f3EmptyMemsetGhostHookNarrow mmpl` (matches H-REV
    `rev_c10_c3.md` R-2 / T-1). -/
theorem f3EmptyMemsetGhostHookNarrow_r1_conj (mmpl : MultiPlacement) :
    (∀ stk, 0 < stk → HookOk (f3EmptyMemsetGhostHookNarrow mmpl) (libcMemsetSpec stk)) ∧
    (∀ stk, 0 < stk → HookOk (f3EmptyMemsetGhostHookNarrow mmpl) (sessionMemsetSpec stk)) ∧
    HookOk (f3EmptyMemsetGhostHookNarrow mmpl) memsetRegionSpec ∧
    HookOk (f3EmptyMemsetGhostHookNarrow mmpl) sessionMemsetRegionSpec ∧
    (∀ s : State, VmPreserved s (f3EmptyMemsetGhostHookNarrow mmpl s)) ∧
    (∀ s : State, (f3EmptyMemsetGhostHookNarrow mmpl s).fs = s.fs) ∧
    HookFsTraced IsFsC (f3EmptyMemsetGhostHookNarrow mmpl) := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_r1_conj mmpl

/-- Direct R1 `memcpy` conjunction on `f3EmptyMemcpyGhostHookNarrow mmpl` (matches H-REV
    `rev_c10_c3.md` R-2 / T-1). -/
theorem f3EmptyMemcpyGhostHookNarrow_r1_conj (mmpl : MultiPlacement) :
    (∀ stk, HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) (libcMemcpySpec stk)) ∧
    (∀ stk, HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) (sessionMemcpySpec stk)) ∧
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) memcpyRegionSpec ∧
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) sessionMemcpyRegionSpec ∧
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) framelessMemcpySpec ∧
    HookOk (f3EmptyMemcpyGhostHookNarrow mmpl) sessionMemcpyRegionROSpec ∧
    (∀ s : State, VmPreserved s (f3EmptyMemcpyGhostHookNarrow mmpl s)) ∧
    (∀ s : State, (f3EmptyMemcpyGhostHookNarrow mmpl s).fs = s.fs) ∧
    HookFsTraced IsFsC (f3EmptyMemcpyGhostHookNarrow mmpl) := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact narrowMemcpyGhostHook_r1_conj mmpl

/-- Exact 1-term existential witness for Stage A `CliGhostAllocHooks.memset` /
    `CliGhostSpqrAllocHooks.memset` (and `cliGhost{,Spqr}AllocHooks_f3CliGhostHooksFixed`). -/
theorem f3EmptyMemsetGhostHookNarrow_r1_allocWitness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (f3EmptyMemsetGhostHookNarrow mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow] at hslot
  exact narrowMemsetGhostHook_r1_allocWitness mmpl hslot

/-- Exact 1-term existential witness for Stage A `CliGhostAllocHooks.memcpy` /
    `CliGhostSpqrAllocHooks.memcpy` (and `cliGhost{,Spqr}AllocHooks_f3CliGhostHooksFixed`). -/
theorem f3EmptyMemcpyGhostHookNarrow_r1_allocWitness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (f3EmptyMemcpyGhostHookNarrow mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f sessionMemcpyRegionROSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow] at hslot
  exact narrowMemcpyGhostHook_r1_allocWitness mmpl hslot

/-- Exact 1-term existential witness for Stage A `CliGhostA0Hooks.memset` (non-budget). -/
theorem f3EmptyMemsetGhostHookNarrow_r1_a0Witness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (f3EmptyMemsetGhostHookNarrow mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow] at hslot
  exact narrowMemsetGhostHook_r1_a0Witness mmpl hslot

/-- Exact 1-term existential witness for Stage A `CliGhostA0Hooks.memcpy` (non-budget). -/
theorem f3EmptyMemcpyGhostHookNarrow_r1_a0Witness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (f3EmptyMemcpyGhostHookNarrow mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f sessionMemcpyRegionROSpec ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f := by
  rw [f3EmptyMemcpyGhostHookNarrow_eq_narrow] at hslot
  exact narrowMemcpyGhostHook_r1_a0Witness mmpl hslot

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
