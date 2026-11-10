/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy -- proof-setup: allow-public-import

/-!
# K-Route Narrow `memset` / `memcpy` R1 Witnesses & CLI-617 Replay (`ElfSlicesPqOomH2KNarrowR1`)

Connects the cycle-free `NarrowF3R1Witness` twins (`f3EmptyMemsetGhostHookNarrow`,
`f3EmptyMemcpyGhostHookNarrow`) to `ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow` and
`ElfSlicesPqOomH2KMemcpy.h2k_memcpyGhostHookNarrow` by **definitional (`rfl`) equality**
(`hole2_emptyProg = emptyStdProg`), closing H-REV Stage A Condition **C2** (`#1255`) and
`rev_c10_c3.md` §3 row 6 at the `h2k_*Narrow` layer:

1. **Definitional (`rfl`) Twin Pins (`rev_c10_c3.md` R-6):**
   - `h2k_memsetGhostHookNarrow_eq_f3Empty : h2k_memsetGhostHookNarrow mmpl = f3EmptyMemsetGhostHookNarrow mmpl := rfl`
   - `h2k_memcpyGhostHookNarrow_eq_f3Empty : h2k_memcpyGhostHookNarrow mmpl = f3EmptyMemcpyGhostHookNarrow mmpl := rfl`
2. **Complete Unconditional R1 / C2 Suite for `h2k_{memset,memcpy}GhostHookNarrow`:**
   - Unconditional `VmPreserved`, `.fs`, `.trace`, `HookFsTraced IsFsC`, `HookNoAllocFailed`, and
     `ExecFrozen` preservation (`0` `LinkedAt` / `Placeable` / `lr` premises);
   - All R1 consumer `HookOk` lifts (including `framelessMemcpySpec` and
     `SpqrV1.Alloc.sessionMemcpyRegionROSpec`), plus `_r1_conj`, `_r1_allocWitness`, and
     `_r1_a0Witness`.
3. **Closed CLI Block-617 `hblk21_ext` / `hblk20_ext` Trap Dischargers & Behind-Stub Replay Wrappers
   (`rev_c10_c3.md` §3 row 6, Route 2 `R2-T1`):**
   - `h2k_ghFixedK_blk21_ext_trap` and `h2k_ghFixedK_blk20_ext_trap`: closed `blk21`/`blk20`
     trap-or-`none` dischargers for `cliProgExtPlacedAt mpl (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W`;
   - Compositional `h2k_cliGhostExterns_ghFixedK_blk20_ext` and
     `h2k_memcpyGhostHookNarrow_stub_replayOn_ghFixedK` (using `h2k_memcpyGhostHookNarrow_blk20TrapHook`
     at `"memcpy"` and stub disjointness only for `"memset"` and `lsRustNoAllocShimSymCli`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KNarrowR1

open Arm64 ProofLib ProofLib.ProgramReflection
open Arm64.Obj (MultiPlacedLib MultiPlacement)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (
  framelessMemcpySpec
  sessionMemcpyRegionSpec sessionMemcpySpec sessionMemsetRegionSpec sessionMemsetSpec
)
open CryptoVerification.SignalSession (
  CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
  lsMemcpySym lsMemsetSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli
  lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC cliGhostExterns)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.Fine (f3MallocngMpl)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (HookNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (keepMemcpyBlk20)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet (Blk20TrapHook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (keepMemsetBlk21)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet (Blk21TrapHook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness (
  f3EmptyMemcpyGhostHookNarrow f3EmptyMemcpyGhostHookNarrow_eq_narrow
  f3EmptyMemcpyGhostHookNarrow_execFrozen f3EmptyMemcpyGhostHookNarrow_framelessMemcpy_ok
  f3EmptyMemcpyGhostHookNarrow_fs f3EmptyMemcpyGhostHookNarrow_fsT
  f3EmptyMemcpyGhostHookNarrow_libcMemcpy_ok f3EmptyMemcpyGhostHookNarrow_memcpyRegion_ok
  f3EmptyMemcpyGhostHookNarrow_noAllocFailed f3EmptyMemcpyGhostHookNarrow_r1_a0Witness
  f3EmptyMemcpyGhostHookNarrow_r1_allocWitness f3EmptyMemcpyGhostHookNarrow_r1_conj
  f3EmptyMemcpyGhostHookNarrow_sessionMemcpyRegionRO_ok
  f3EmptyMemcpyGhostHookNarrow_sessionMemcpyRegion_ok
  f3EmptyMemcpyGhostHookNarrow_sessionMemcpy_ok
  f3EmptyMemcpyGhostHookNarrow_trace f3EmptyMemcpyGhostHookNarrow_vmPreserved
  f3EmptyMemsetGhostHookNarrow f3EmptyMemsetGhostHookNarrow_eq_narrow
  f3EmptyMemsetGhostHookNarrow_execFrozen f3EmptyMemsetGhostHookNarrow_fs
  f3EmptyMemsetGhostHookNarrow_fsT f3EmptyMemsetGhostHookNarrow_libcMemset_ok
  f3EmptyMemsetGhostHookNarrow_memsetRegion_ok f3EmptyMemsetGhostHookNarrow_noAllocFailed
  f3EmptyMemsetGhostHookNarrow_r1_a0Witness f3EmptyMemsetGhostHookNarrow_r1_allocWitness
  f3EmptyMemsetGhostHookNarrow_r1_conj f3EmptyMemsetGhostHookNarrow_sessionMemsetRegion_ok
  f3EmptyMemsetGhostHookNarrow_sessionMemset_ok
  f3EmptyMemsetGhostHookNarrow_trace f3EmptyMemsetGhostHookNarrow_vmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1 (
  narrowMemcpyGhostHook narrowMemsetGhostHook
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (
  f3LsSymAddrs lsInternedMultiLib lsSharedExterns ls_blockSymsMatch_ok
  ls_idsOk ls_names_nodup ls_sharedExterns_lt ls_toMultiPlacedLib_eq
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced (
  f3CliElf_libsignal_inElf_unique f3CliElf_mallocng_linkedAt_unique f3TrialElf_parse
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy (
  h2k_ghFixedK_blk20TrapHook h2k_keepSub_covers_blk20 h2k_memcpyGhostHookNarrow
  h2k_memcpyGhostHookNarrow_blk20TrapHook h2k_memcpyGhostHookNarrow_stub_replayOn_of_trap_ret
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset (
  h2k_ghFixedK_blk21TrapHook h2k_keepSub_covers_blk21 h2k_memsetGhostHookNarrow
  h2k_shimStub_not_in_blk21
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2 (
  h2sl_realW_noExtern_keepSub
)
open VerifiedLibraries (mallocngLib)

/-! ## 1. Definitional (`rfl`) Twin Pins (`rev_c10_c3.md` R-6) -/

theorem h2k_memsetGhostHookNarrow_eq_f3Empty (mmpl : MultiPlacement) :
    h2k_memsetGhostHookNarrow mmpl = f3EmptyMemsetGhostHookNarrow mmpl := rfl

theorem h2k_memcpyGhostHookNarrow_eq_f3Empty (mmpl : MultiPlacement) :
    h2k_memcpyGhostHookNarrow mmpl = f3EmptyMemcpyGhostHookNarrow mmpl := rfl

theorem h2k_memsetGhostHookNarrow_eq_narrow (mmpl : MultiPlacement) :
    h2k_memsetGhostHookNarrow mmpl = narrowMemsetGhostHook mmpl :=
  f3EmptyMemsetGhostHookNarrow_eq_narrow mmpl

theorem h2k_memcpyGhostHookNarrow_eq_narrow (mmpl : MultiPlacement) :
    h2k_memcpyGhostHookNarrow mmpl = narrowMemcpyGhostHook mmpl :=
  f3EmptyMemcpyGhostHookNarrow_eq_narrow mmpl

/-! ## 2. `h2k_memsetGhostHookNarrow` Unconditional R1 / C2 Suite -/

theorem h2k_memsetGhostHookNarrow_vmPreserved (mmpl : MultiPlacement) (s : State) :
    VmPreserved s (h2k_memsetGhostHookNarrow mmpl s) :=
  f3EmptyMemsetGhostHookNarrow_vmPreserved mmpl s

theorem h2k_memsetGhostHookNarrow_fs (mmpl : MultiPlacement) (s : State) :
    (h2k_memsetGhostHookNarrow mmpl s).fs = s.fs :=
  f3EmptyMemsetGhostHookNarrow_fs mmpl s

theorem h2k_memsetGhostHookNarrow_fsT (mmpl : MultiPlacement) :
    HookFsTraced IsFsC (h2k_memsetGhostHookNarrow mmpl) :=
  f3EmptyMemsetGhostHookNarrow_fsT mmpl

theorem h2k_memsetGhostHookNarrow_trace (mmpl : MultiPlacement) (s : State) :
    (h2k_memsetGhostHookNarrow mmpl s).trace = s.trace :=
  f3EmptyMemsetGhostHookNarrow_trace mmpl s

theorem h2k_memsetGhostHookNarrow_noAllocFailed (mmpl : MultiPlacement) :
    HookNoAllocFailed (h2k_memsetGhostHookNarrow mmpl) :=
  f3EmptyMemsetGhostHookNarrow_noAllocFailed mmpl

theorem h2k_memsetGhostHookNarrow_execFrozen (mmpl : MultiPlacement) (s : State)
    (hfr : ExecFrozen s.mem) :
    ExecFrozen (h2k_memsetGhostHookNarrow mmpl s).mem :=
  f3EmptyMemsetGhostHookNarrow_execFrozen mmpl s hfr

theorem h2k_memsetGhostHookNarrow_libcMemset_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookNarrow mmpl) (libcMemsetSpec stk) :=
  f3EmptyMemsetGhostHookNarrow_libcMemset_ok mmpl stk

theorem h2k_memsetGhostHookNarrow_sessionMemset_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookNarrow mmpl) (sessionMemsetSpec stk) :=
  f3EmptyMemsetGhostHookNarrow_sessionMemset_ok mmpl stk

theorem h2k_memsetGhostHookNarrow_memsetRegion_ok (mmpl : MultiPlacement) :
    HookOk (h2k_memsetGhostHookNarrow mmpl) memsetRegionSpec :=
  f3EmptyMemsetGhostHookNarrow_memsetRegion_ok mmpl

/-- R1-routed alias for `ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow_sessionMemsetRegion_ok`
    (suffixed `_r1_ok` to avoid shadowing when opening both `ElfSlicesPqOomH2KMemset` and
    `ElfSlicesPqOomH2KNarrowR1`). -/
theorem h2k_memsetGhostHookNarrow_sessionMemsetRegion_r1_ok (mmpl : MultiPlacement) :
    HookOk (h2k_memsetGhostHookNarrow mmpl) sessionMemsetRegionSpec :=
  f3EmptyMemsetGhostHookNarrow_sessionMemsetRegion_ok mmpl

theorem h2k_memsetGhostHookNarrow_r1_conj (mmpl : MultiPlacement) :
    (∀ stk, 0 < stk → HookOk (h2k_memsetGhostHookNarrow mmpl) (libcMemsetSpec stk)) ∧
    (∀ stk, 0 < stk → HookOk (h2k_memsetGhostHookNarrow mmpl) (sessionMemsetSpec stk)) ∧
    HookOk (h2k_memsetGhostHookNarrow mmpl) memsetRegionSpec ∧
    HookOk (h2k_memsetGhostHookNarrow mmpl) sessionMemsetRegionSpec ∧
    (∀ s : State, VmPreserved s (h2k_memsetGhostHookNarrow mmpl s)) ∧
    (∀ s : State, (h2k_memsetGhostHookNarrow mmpl s).fs = s.fs) ∧
    HookFsTraced IsFsC (h2k_memsetGhostHookNarrow mmpl) :=
  f3EmptyMemsetGhostHookNarrow_r1_conj mmpl

theorem h2k_memsetGhostHookNarrow_r1_allocWitness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (h2k_memsetGhostHookNarrow mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f :=
  f3EmptyMemsetGhostHookNarrow_r1_allocWitness mmpl hslot

theorem h2k_memsetGhostHookNarrow_r1_a0Witness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (h2k_memsetGhostHookNarrow mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f :=
  f3EmptyMemsetGhostHookNarrow_r1_a0Witness mmpl hslot

/-! ## 3. `h2k_memcpyGhostHookNarrow` Unconditional R1 / C2 Suite -/

theorem h2k_memcpyGhostHookNarrow_vmPreserved (mmpl : MultiPlacement) (s : State) :
    VmPreserved s (h2k_memcpyGhostHookNarrow mmpl s) :=
  f3EmptyMemcpyGhostHookNarrow_vmPreserved mmpl s

theorem h2k_memcpyGhostHookNarrow_fs (mmpl : MultiPlacement) (s : State) :
    (h2k_memcpyGhostHookNarrow mmpl s).fs = s.fs :=
  f3EmptyMemcpyGhostHookNarrow_fs mmpl s

theorem h2k_memcpyGhostHookNarrow_fsT (mmpl : MultiPlacement) :
    HookFsTraced IsFsC (h2k_memcpyGhostHookNarrow mmpl) :=
  f3EmptyMemcpyGhostHookNarrow_fsT mmpl

theorem h2k_memcpyGhostHookNarrow_trace (mmpl : MultiPlacement) (s : State) :
    (h2k_memcpyGhostHookNarrow mmpl s).trace = s.trace :=
  f3EmptyMemcpyGhostHookNarrow_trace mmpl s

theorem h2k_memcpyGhostHookNarrow_noAllocFailed (mmpl : MultiPlacement) :
    HookNoAllocFailed (h2k_memcpyGhostHookNarrow mmpl) :=
  f3EmptyMemcpyGhostHookNarrow_noAllocFailed mmpl

theorem h2k_memcpyGhostHookNarrow_execFrozen (mmpl : MultiPlacement) (s : State)
    (hfr : ExecFrozen s.mem) :
    ExecFrozen (h2k_memcpyGhostHookNarrow mmpl s).mem :=
  f3EmptyMemcpyGhostHookNarrow_execFrozen mmpl s hfr

theorem h2k_memcpyGhostHookNarrow_libcMemcpy_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookNarrow mmpl) (libcMemcpySpec stk) :=
  f3EmptyMemcpyGhostHookNarrow_libcMemcpy_ok mmpl stk

theorem h2k_memcpyGhostHookNarrow_sessionMemcpy_ok (mmpl : MultiPlacement) (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookNarrow mmpl) (sessionMemcpySpec stk) :=
  f3EmptyMemcpyGhostHookNarrow_sessionMemcpy_ok mmpl stk

theorem h2k_memcpyGhostHookNarrow_memcpyRegion_ok (mmpl : MultiPlacement) :
    HookOk (h2k_memcpyGhostHookNarrow mmpl) memcpyRegionSpec :=
  f3EmptyMemcpyGhostHookNarrow_memcpyRegion_ok mmpl

theorem h2k_memcpyGhostHookNarrow_sessionMemcpyRegion_ok (mmpl : MultiPlacement) :
    HookOk (h2k_memcpyGhostHookNarrow mmpl) sessionMemcpyRegionSpec :=
  f3EmptyMemcpyGhostHookNarrow_sessionMemcpyRegion_ok mmpl

theorem h2k_memcpyGhostHookNarrow_framelessMemcpy_ok (mmpl : MultiPlacement) :
    HookOk (h2k_memcpyGhostHookNarrow mmpl) framelessMemcpySpec :=
  f3EmptyMemcpyGhostHookNarrow_framelessMemcpy_ok mmpl

theorem h2k_memcpyGhostHookNarrow_sessionMemcpyRegionRO_ok (mmpl : MultiPlacement) :
    HookOk (h2k_memcpyGhostHookNarrow mmpl) sessionMemcpyRegionROSpec :=
  f3EmptyMemcpyGhostHookNarrow_sessionMemcpyRegionRO_ok mmpl

theorem h2k_memcpyGhostHookNarrow_r1_conj (mmpl : MultiPlacement) :
    (∀ stk, HookOk (h2k_memcpyGhostHookNarrow mmpl) (libcMemcpySpec stk)) ∧
    (∀ stk, HookOk (h2k_memcpyGhostHookNarrow mmpl) (sessionMemcpySpec stk)) ∧
    HookOk (h2k_memcpyGhostHookNarrow mmpl) memcpyRegionSpec ∧
    HookOk (h2k_memcpyGhostHookNarrow mmpl) sessionMemcpyRegionSpec ∧
    HookOk (h2k_memcpyGhostHookNarrow mmpl) framelessMemcpySpec ∧
    HookOk (h2k_memcpyGhostHookNarrow mmpl) sessionMemcpyRegionROSpec ∧
    (∀ s : State, VmPreserved s (h2k_memcpyGhostHookNarrow mmpl s)) ∧
    (∀ s : State, (h2k_memcpyGhostHookNarrow mmpl s).fs = s.fs) ∧
    HookFsTraced IsFsC (h2k_memcpyGhostHookNarrow mmpl) :=
  f3EmptyMemcpyGhostHookNarrow_r1_conj mmpl

theorem h2k_memcpyGhostHookNarrow_r1_allocWitness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (h2k_memcpyGhostHookNarrow mmpl) := by rfl) :
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
  f3EmptyMemcpyGhostHookNarrow_r1_allocWitness mmpl hslot

theorem h2k_memcpyGhostHookNarrow_r1_a0Witness (mmpl : MultiPlacement)
    {slot : Option (State → State)}
    (hslot : slot = some (h2k_memcpyGhostHookNarrow mmpl) := by rfl) :
    ∃ f, slot = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f sessionMemcpyRegionROSpec ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f :=
  f3EmptyMemcpyGhostHookNarrow_r1_a0Witness mmpl hslot

/-! ## 4. Closed CLI Block-`617` `hblk20_ext` & Behind-Stub Replays (`rev_c10_c3.md` §3 row 6) -/

private theorem externAt?_cliProgExtPlacedAt_any
    (mpl : MultiPlacement) (extFn : CliHooks → String → Option (State → State))
    (W : CliHooks) (pc : BitVec 64) :
    (cliProgExtPlacedAt mpl extFn 617 W).externAt? pc =
      (libsignalSessionLib.blockLib 617).text.externs.findSome? fun e =>
        if libsignalSessionLib.resolve mpl e == pc then extFn W e else none := by
  have key : ∀ (b : BitVec 64) (e : String),
      ((libsignalSessionLib.resolve mpl e - b).toNat == (pc - b).toNat) =
        (libsignalSessionLib.resolve mpl e == pc) := by
    intro b e
    cases h : libsignalSessionLib.resolve mpl e == pc with
    | true => have heq := beq_iff_eq.mp h; subst heq; simp
    | false =>
      rw [beq_eq_false_iff_ne] at h ⊢
      intro hnat; apply h
      have := congrArg (· + b) (BitVec.eq_of_toNat_eq hnat)
      simpa [BitVec.sub_add_cancel] using this
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  dsimp only [cliProgExtPlacedAt, MultiPlacedLib.blockProgram, Arm64.Obj.PlacedLib.program,
    MultiPlacedLib.blockPlacement, Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0, Option.or_none, List.findSome?_map, Function.comp_def, key]

private theorem exists_of_findSome?_eq_some {α β : Type} {l : List α} {g : α → Option β} {y : β}
    (h : l.findSome? g = some y) : ∃ x ∈ l, g x = some y := by
  induction l with
  | nil => cases h
  | cons a tl ih =>
    simp only [List.findSome?_cons] at h
    cases hga : g a with
    | some v => rw [hga] at h; injection h with hv; subst hv; exact ⟨a, List.mem_cons_self, hga⟩
    | none =>
      rw [hga] at h; obtain ⟨x, hx, hgx⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem _ hx, hgx⟩

private theorem findSome?_eq_none_imp {α β : Type} {l : List α} {g : α → Option β}
    (h : l.findSome? g = none) {x : α} (hx : x ∈ l) : g x = none := by
  induction l with
  | nil => cases hx
  | cons a tl ih =>
    simp only [List.findSome?_cons] at h
    cases hga : g a with
    | some _ => rw [hga] at h; cases h
    | none =>
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact hga
      · rw [hga] at h; exact ih h hxtl

private theorem resolve_idx_of_linkedAt {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {idx : Nat} (hidx : idx ∈ lsSharedExterns) :
    libsignalSessionLib.resolve mpl (lsInternedMultiLib.names.getD idx "") =
      f3LsSymAddrs.getD idx 0#64 := by
  obtain ⟨_, hp, hpl, hin⟩ := hLs
  cases f3TrialElf_parse.symm.trans hp
  have hlt : idx < lsInternedMultiLib.names.length :=
    Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx)
  have hmem : lsInternedMultiLib.names.getD idx "" ∈ lsInternedMultiLib.names := by
    rw [Arm64.Obj.Interned.getD_of_lt hlt]; exact List.getElem_mem hlt
  rw [(f3CliElf_libsignal_inElf_unique hpl hin).2.1 _ hmem, ls_toMultiPlacedLib_eq]
  change lsInternedMultiLib.toMultiPlacedLib.resolve
    (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.f3LsLayout.toMultiPlacement
      lsInternedMultiLib.names) _ = _
  rw [Arm64.Obj.Interned.toMultiPlacement_resolve_eq ls_names_nodup ls_idsOk ls_blockSymsMatch_ok,
    Arm64.Obj.Interned.idxOf_getD ls_names_nodup hlt]
  rfl

private theorem keepMemcpyBlk20_eq_f3 {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    keepMemcpyBlk20 mmpl = keepMemcpyBlk20 f3MallocngMpl := by
  funext a; unfold keepMemcpyBlk20
  have h20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  rw [(f3CliElf_mallocng_linkedAt_unique hMm).1 20 h20]

private noncomputable def h2k_shimDisjointBlk20B : Bool :=
  lsSharedExterns.any fun idx =>
    (lsInternedMultiLib.names.getD idx "" == lsRustNoAllocShimSymCli) &&
    !(keepMemcpyBlk20 f3MallocngMpl (f3LsSymAddrs.getD idx 0#64))

set_option maxRecDepth 4000000 in
private theorem h2k_shimDisjointBlk20_ok : h2k_shimDisjointBlk20B = true := by rfl_kernel

/-- The `lsRustNoAllocShimSymCli` stub PC lies outside `keepMemcpyBlk20 mmpl` on 39-row
    `cliElfBytes` (proof shape intended to carry over to 37-row stock-lld; re-proved at re-key). -/
theorem h2k_shimStub_not_in_blk20 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    keepMemcpyBlk20 mmpl (libsignalSessionLib.resolve mpl lsRustNoAllocShimSymCli) = false := by
  obtain ⟨idx, hidx, hpred⟩ := List.any_eq_true.mp h2k_shimDisjointBlk20_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  rw [keepMemcpyBlk20_eq_f3 hMm, ← hpred.1, resolve_idx_of_linkedAt hLs hidx]
  cases hb : keepMemcpyBlk20 f3MallocngMpl (f3LsSymAddrs.getD idx 0#64)
  · rfl
  · rw [hb] at hpred; cases hpred.2

private noncomputable def h2k_memsetDisjointBlk20B : Bool :=
  lsSharedExterns.any fun idx =>
    (lsInternedMultiLib.names.getD idx "" == "memset") &&
    !(keepMemcpyBlk20 f3MallocngMpl (f3LsSymAddrs.getD idx 0#64))

set_option maxRecDepth 4000000 in
private theorem h2k_memsetDisjointBlk20_ok : h2k_memsetDisjointBlk20B = true := by rfl_kernel

/-- The `"memset"` resolution address lies outside `keepMemcpyBlk20 mmpl` on 39-row `cliElfBytes`
    (proof shape intended to carry over to 37-row stock-lld where `"memset"` resolves to
    `mmpl.base 21 ∉ blk20`; re-proved at re-key). -/
theorem h2k_memsetStub_not_in_blk20 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    keepMemcpyBlk20 mmpl (libsignalSessionLib.resolve mpl "memset") = false := by
  obtain ⟨idx, hidx, hpred⟩ := List.any_eq_true.mp h2k_memsetDisjointBlk20_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  rw [keepMemcpyBlk20_eq_f3 hMm, ← hpred.1, resolve_idx_of_linkedAt hLs hidx]
  cases hb : keepMemcpyBlk20 f3MallocngMpl (f3LsSymAddrs.getD idx 0#64)
  · rfl
  · rw [hb] at hpred; cases hpred.2

private theorem cliGhostExterns_some_cases (g : CliGhostHooks)
    (baseExt : String → Option (State → State)) {sym : String} {f : State → State}
    (hext : cliGhostExterns g baseExt sym = some f) :
    sym = lsRustNoAllocShimSymCli ∨
      (sym ≠ lsRustNoAllocShimSymCli ∧ cliGhostExterns g (fun _ => none) sym = some f) ∨
      baseExt sym = some f := by
  by_cases h5 : sym = lsRustNoAllocShimSymCli
  · exact Or.inl h5
  · refine Or.inr ?_
    unfold cliGhostExterns at hext ⊢
    by_cases h1 : sym == lsRustAllocSymCli
    · simp only [h1, ↓reduceIte] at hext ⊢; exact Or.inl ⟨h5, hext⟩
    · by_cases h2 : sym == lsRustDeallocSymCli
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at hext ⊢; exact Or.inl ⟨h5, hext⟩
      · by_cases h3 : sym == lsRustReallocSymCli
        · simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte] at hext ⊢; exact Or.inl ⟨h5, hext⟩
        · by_cases h4 : sym == lsRustAllocZeroedSymCli
          · simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at hext ⊢
            exact Or.inl ⟨h5, hext⟩
          · have h5b : (sym == lsRustNoAllocShimSymCli) = false := beq_eq_false_iff_ne.mpr h5
            simp only [h1, h2, h3, h4, h5b, Bool.false_eq_true, ↓reduceIte] at hext ⊢
            by_cases h6 : sym == lsStringCloneSym
            · cases hsc : g.stringClone <;> simp only [h6, hsc, ↓reduceIte] at hext ⊢
              · exact Or.inr hext
              · exact Or.inl ⟨h5, hext⟩
            · by_cases h7 : sym == lsReadFileSym
              · cases hrf : g.readFile <;>
                  simp only [h6, h7, hrf, Bool.false_eq_true, ↓reduceIte] at hext ⊢
                · exact Or.inr hext
                · exact Or.inl ⟨h5, hext⟩
              · by_cases h8 : sym == lsReadStdinSym
                · cases hrs : g.readStdin <;>
                    simp only [h6, h7, h8, hrs, Bool.false_eq_true, ↓reduceIte] at hext ⊢
                  · exact Or.inr hext
                  · exact Or.inl ⟨h5, hext⟩
                · by_cases h9 : sym == lsMemsetSym
                  · cases hms : g.memset <;>
                      simp only [h6, h7, h8, h9, hms, Bool.false_eq_true, ↓reduceIte] at hext ⊢
                    · exact Or.inr hext
                    · exact Or.inl ⟨h5, hext⟩
                  · by_cases h10 : sym == lsMemcpySym
                    · cases hmc : g.memcpy <;>
                        simp only [h6, h7, h8, h9, h10, hmc, Bool.false_eq_true, ↓reduceIte] at hext ⊢
                      · exact Or.inr hext
                      · exact Or.inl ⟨h5, hext⟩
                    · simp only [h6, h7, h8, h9, h10, Bool.false_eq_true, ↓reduceIte] at hext
                      exact Or.inr hext

/-- **Closed `P_ghost` `blk21` trap-or-`none` discharger for `h2k_ghFixedK` (`R2-T1`):**
    for every `pc` with `keepMemsetBlk21 mmpl pc = true`, the Block-617 ghost program
    `cliProgExtPlacedAt mpl (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W`
    either has `externAt? pc = none` or dispatches to a hook `f` satisfying
    `∀ L, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f`. -/
theorem h2k_ghFixedK_blk21_ext_trap [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f := by
  intro pc hpc
  cases hg : (cliProgExtPlacedAt mpl
    (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
    617 W).externAt? pc with
  | none => exact Or.inl rfl
  | some f =>
    refine Or.inr ⟨f, rfl, ?_⟩
    rw [externAt?_cliProgExtPlacedAt_any] at hg
    obtain ⟨sym, hsym_mem, hsym_ite⟩ := exists_of_findSome?_eq_some hg
    cases hres_eq : libsignalSessionLib.resolve mpl sym == pc with
    | false => rw [hres_eq] at hsym_ite; cases hsym_ite
    | true =>
      rw [hres_eq] at hsym_ite; simp only [↓reduceIte] at hsym_ite
      have hres : libsignalSessionLib.resolve mpl sym = pc := beq_iff_eq.mp hres_eq
      rcases cliGhostExterns_some_cases (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) hsym_ite with
        rfl | ⟨hne, hgh⟩ | hbase
      · exfalso; have hns := h2k_shimStub_not_in_blk21 hLs hMm
        rw [hres, hpc] at hns; exact Bool.noConfusion hns
      · exact h2k_ghFixedK_blk21TrapHook mpl hMm hgh hne
      · exfalso
        have hreal_none :=
          h2sl_realW_noExtern_keepSub hLs mmpl W pc (h2k_keepSub_covers_blk21 hMm pc hpc)
        rw [externAt?_cliProgExtPlacedAt_any] at hreal_none
        have hcell := findSome?_eq_none_imp hreal_none hsym_mem
        rw [hres_eq, hbase] at hcell; cases hcell

/-- **Closed `P_ghost` `blk20` trap-or-`none` discharger for `h2k_ghFixedK` (`R2-T1`):**
    for every `pc` with `keepMemcpyBlk20 mmpl pc = true`, the Block-617 ghost program
    `cliProgExtPlacedAt mpl (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W`
    either has `externAt? pc = none` or dispatches to a hook `f` satisfying
    `∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f`. -/
theorem h2k_ghFixedK_blk20_ext_trap [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f := by
  intro pc hpc
  cases hg : (cliProgExtPlacedAt mpl
    (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
    617 W).externAt? pc with
  | none => exact Or.inl rfl
  | some f =>
    refine Or.inr ⟨f, rfl, ?_⟩
    rw [externAt?_cliProgExtPlacedAt_any] at hg
    obtain ⟨sym, hsym_mem, hsym_ite⟩ := exists_of_findSome?_eq_some hg
    cases hres_eq : libsignalSessionLib.resolve mpl sym == pc with
    | false => rw [hres_eq] at hsym_ite; cases hsym_ite
    | true =>
      rw [hres_eq] at hsym_ite; simp only [↓reduceIte] at hsym_ite
      have hres : libsignalSessionLib.resolve mpl sym = pc := beq_iff_eq.mp hres_eq
      rcases cliGhostExterns_some_cases (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) hsym_ite with
        rfl | ⟨hne, hgh⟩ | hbase
      · exfalso; have hns := h2k_shimStub_not_in_blk20 hLs hMm
        rw [hres, hpc] at hns; exact Bool.noConfusion hns
      · exact h2k_ghFixedK_blk20TrapHook mpl hMm hgh hne
      · exfalso
        have hreal_none :=
          h2sl_realW_noExtern_keepSub hLs mmpl W pc (h2k_keepSub_covers_blk20 hMm pc hpc)
        rw [externAt?_cliProgExtPlacedAt_any] at hreal_none
        have hcell := findSome?_eq_none_imp hreal_none hsym_mem
        rw [hres_eq, hbase] at hcell; cases hcell

/-- **Compositional ghost-side `hblk20_ext` on 39-row `cliElfBytes`:** combines
    `h2k_ghFixedK_blk20TrapHook` (7 K ghosts), `h2k_memcpyGhostHookNarrow_blk20TrapHook`
    (`"memcpy"`), `h2k_memsetStub_not_in_blk20` (`"memset"`), `h2k_shimStub_not_in_blk20` (`shim`),
    and `h2sl_realW_noExtern_keepSub` on any base map `baseExt ⊆ cliExternsPlaced mmpl` (proof
    shape intended to carry over to 37-row stock-lld where `resolve mpl "memcpy" = mmpl.base 20`;
    re-proved at re-key). -/
theorem h2k_cliGhostExterns_ghFixedK_blk20_ext [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (baseExt : CliHooks → String → Option (State → State))
    (hbase_sub : ∀ W sym, baseExt W sym = none ∨ baseExt W sym = cliExternsPlaced mmpl W sym)
    (W : CliHooks) :
    let P_ghost := cliProgExtPlacedAt mpl
      (fun W' sym =>
        if sym == "memcpy" then some (h2k_memcpyGhostHookNarrow mmpl)
        else if sym == "memset" then some (h2k_memsetGhostHookNarrow mmpl)
        else cliGhostExterns (h2k_ghFixedK mpl mmpl) (baseExt W') sym) 617 W
    ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f := by
  intro P_ghost pc hpc
  cases hg : P_ghost.externAt? pc with
  | none => exact Or.inl rfl
  | some f =>
    refine Or.inr ⟨f, rfl, ?_⟩
    rw [externAt?_cliProgExtPlacedAt_any] at hg
    obtain ⟨sym, hsym_mem, hsym_ite⟩ := exists_of_findSome?_eq_some hg
    cases hres_eq : libsignalSessionLib.resolve mpl sym == pc with
    | false => rw [hres_eq] at hsym_ite; cases hsym_ite
    | true =>
      rw [hres_eq] at hsym_ite; simp only [↓reduceIte] at hsym_ite
      have hres : libsignalSessionLib.resolve mpl sym = pc := beq_iff_eq.mp hres_eq
      by_cases hmc : sym == "memcpy"
      · simp only [hmc, ↓reduceIte, Option.some.injEq] at hsym_ite; subst hsym_ite
        exact h2k_memcpyGhostHookNarrow_blk20TrapHook mmpl
      · simp only [hmc, Bool.false_eq_true, ↓reduceIte] at hsym_ite
        by_cases hms : sym == "memset"
        · exfalso
          have hsym_ms : sym = "memset" := beq_iff_eq.mp hms
          subst hsym_ms
          have hns := h2k_memsetStub_not_in_blk20 hLs hMm
          rw [hres, hpc] at hns; exact Bool.noConfusion hns
        · simp only [hms, Bool.false_eq_true, ↓reduceIte] at hsym_ite
          rcases cliGhostExterns_some_cases (h2k_ghFixedK mpl mmpl) (baseExt W) hsym_ite with
            rfl | ⟨hne, hgh⟩ | hbase
          · exfalso; have hns := h2k_shimStub_not_in_blk20 hLs hMm
            rw [hres, hpc] at hns; exact Bool.noConfusion hns
          · exact h2k_ghFixedK_blk20TrapHook mpl hMm hgh hne
          · exfalso
            rcases hbase_sub W sym with hnone | heq_real
            · rw [hnone] at hbase; cases hbase
            · rw [heq_real] at hbase
              have hreal_none :=
                h2sl_realW_noExtern_keepSub hLs mmpl W pc (h2k_keepSub_covers_blk20 hMm pc hpc)
              rw [externAt?_cliProgExtPlacedAt_any] at hreal_none
              have hcell := findSome?_eq_none_imp hreal_none hsym_mem
              rw [hres_eq, hbase] at hcell; cases hcell

/-- **Compositional behind-stub `On` replay for `h2k_memcpyGhostHookNarrow` on 39-row
    `cliElfBytes`:** discharges `hblk20_ext` via `h2k_cliGhostExterns_ghFixedK_blk20_ext` (proof
    shape intended to carry over to 37-row stock-lld where `resolve mpl "memcpy" = mmpl.base 20`;
    re-proved at re-key). -/
theorem h2k_memcpyGhostHookNarrow_stub_replayOn_ghFixedK [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (baseExt : CliHooks → String → Option (State → State))
    (hbase_sub : ∀ W sym, baseExt W sym = none ∨ baseExt W sym = cliExternsPlaced mmpl W sym)
    (W : CliHooks)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc =
      none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 20))
    {sf : State}
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    let f_mc := h2k_memcpyGhostHookNarrow mmpl
    let extFn := fun W' sym =>
      if sym == "memcpy" then some (h2k_memcpyGhostHookNarrow mmpl)
      else if sym == "memset" then some (h2k_memsetGhostHookNarrow mmpl)
      else cliGhostExterns (h2k_ghFixedK mpl mmpl) (baseExt W') sym
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none ∧
    ∀ u : State,
      Steps (cliProgExtPlacedAt mpl extFn 617 W) (f_mc u) sf →
      u.pc = stubPc → u.status = .Running →
      (∀ msg, (f_mc u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f_mc u).mem → ExecFrozen u.mem → F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f_mc u) ∧
        ExecFrozen (f_mc u).mem ∧ F3CodeInv mpl mmpl (f_mc u).mem ∧ (f_mc u).fs = u.fs :=
  h2k_memcpyGhostHookNarrow_stub_replayOn_of_trap_ret hLs hMm W
    (h2k_cliGhostExterns_ghFixedK_blk20_ext hLs hMm baseExt hbase_sub W)
    hreal_stub_none hStub hrun_sf' hnoex_sf hnhalt_sf

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KNarrowR1
