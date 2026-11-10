/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.F3LayoutData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetKeepLrOfOutcome -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import ProofLib.ProgramReflection -- proof-setup: allow-public-import

/-!
# Layout-Generic Startup `lr` Guards, `W`-Independent Harness Corollaries & `Block617TransferFixedHypG` (`ElfMemsetEntryGuard`)

Delivers Card `H-C8` **D3** + Card `W2-C8` **S3b** (`CliElfLib`-rooted, `0` imports from
`ElfSlicesPqOomPlacedInst` or any of the 12 WP4 files, `0` hex address literals):

1. **`"memset"` & `"memcpy"` stub resolution + `LinkedAt` uniqueness + startup `lr` checks (§§1–2):**
   - Discharges `keepMemsetBlk21 mmpl (sm.readReg64 .lr) = false`, `sm.readReg64 .lr ≠ mpl.ρ "memset"`,
     `keepMemcpyBlk20 mmpl (sm.readReg64 .lr) = false`, `sm.readReg64 .lr ≠ mpl.ρ "memcpy"`,
     `F3MemsetEntryGuard mpl mmpl sm`, `F3MemcpyEntryGuard mpl mmpl sm`,
     `F3MemsetMemcpyEntryLrFalse mmpl sm`, and `keepMemOps mmpl (sm.readReg64 .lr) = false`
     from `StdMainEntryLr f3StdLayout sm` (`sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64`)
     and `LinkedAt cliElfBytes` witnesses for `mpl` / `mmpl`.
2. **`W`-independent guarded-harness corollaries (§3):**
   - Consumes `StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt` via `.mono_guard` to yield
     `MuslHarnessFineNeedLocksGuardedPerInput` at the `W`-independent entry guards
     `fun sm => keepMemsetBlk21 mmpl (sm.readReg64 .lr) = false`,
     `fun sm => keepMemcpyBlk20 mmpl (sm.readReg64 .lr) = false`,
     `F3MemsetMemcpyEntryLrFalse mmpl`, `fun sm => keepMemOps mmpl (sm.readReg64 .lr) = false`,
     `F3MemsetEntryGuard mpl mmpl`, `F3MemcpyEntryGuard mpl mmpl`, and their conjunction.
3. **`Block617TransferFixedHypG` instances via `block617TransferFixedG_of_replaysOn_outcome` (§4):**
   - General K-pass-ready combinators (`f3Block617TransferFixedG_of_entryLrFalse_outcome_keep` for
     arbitrary `keep : BitVec 64 → Bool`, and `f3Block617TransferFixedG_of_entryLrFalse_outcome` at
     `keep := fun _ => false` closing `hlr_calls` by `rfl`, plus `StdMainEntryLr f3StdLayout`
     specializations) over arbitrary `EG` / `ER` on `(F3CodeOk mpl mmpl, F3CodeInv mpl mmpl)`.
   - Concrete narrow-ghost instances for `memset`-only (`f3Block617TransferFixedG_memset_of_replaysOn_outcome`
     / `_of_stdMainEntryLr`) and simultaneous `memset` + `memcpy`
     (`f3Block617TransferFixedG_memsetMemcpy_of_replaysOn_outcome` / `_of_stdMainEntryLr`); per
     `rev_c6` F2 / `rev_c8` T2, those concrete wrappers equate `EG` and `ER` outside `memset`
     (resp. `memset`/`memcpy`) via `hother`, whereas the general `f3Block617TransferFixedG_of_*`
     combinators apply directly to the multi-hook K CLI pass without `hother`.

*Scoped-G1 & consumer note:* `Block617TransferFixedHypG` with a non-trivial `Guard` is weaker than
the trusted `Block617TransferFixedHyp` (`rev_c8` T4), and through `decide` / `rfl_kernel` on pinned
F3 data (`f3StdLayout`, `f3MallocngMpl`, `lsPlacedStubPairs`), this module sits on the scoped-G1
frontier; static layout-independence holds with `0` hex literals.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement mallocngBlockProg)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliElfBytes cliElfImage cliExternsPlaced cliProcessInputs libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open LibsignalBinary.Heap.Fine (f3MallocngMpl f3StdLayout fineCostModel)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MuslHarnessFineNeedLocksGuardedPerInput StdMainEntryLr cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt codeLoaded_cliProgExtPlaced_of_codeRoLoaded
   patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (GhostExternReplaysOn StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG block617TransferFixedG_of_replaysOn_outcome
   subroutineOutcome_running_pc_and_noFault)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost
  (keepMemOps keepMemcpyBlk20 memcpyGhostHookBlk20 memcpyGhostHook_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn
  (ghostExternReplaysOn_memcpyGhostHookNarrow_of_trap_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet (Blk20TrapHook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
  (keepMemsetBlk21 memsetGhostHookBlk21 memsetGhostHook_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn
  (ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetKeepLrOfOutcome
  (F3MemsetEntryGuard MemsetEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet (Blk21TrapHook)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (f3LsSymAddrs lsInternedMultiLib lsPlacedStubPairs lsPlacedStubPairs_eq lsSharedExterns ls_idsOk
   ls_names_nodup ls_sharedExterns_lt ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_libsignal_linkedAt_unique f3CliElf_mallocng_linkedAt_unique f3LsMpl)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv F3CodeOk cliElf_f3MuslHarnessLr_of_linkedAt)

/-! ## 1. `libsignalSessionLib` `"memset"` Stub Resolution & `LinkedAt` Uniqueness -/

noncomputable section

private def findStubPosAux (target : String) : List (String × BitVec 64) → Nat → Nat
  | [], acc => acc
  | (nm, _) :: rest, acc =>
    if nm == target then acc else findStubPosAux target rest (acc + 1)

private def lsMemsetExternPos : Nat :=
  findStubPosAux "memset" lsPlacedStubPairs 0

private def lsMemsetIdx : Nat :=
  lsSharedExterns.getD lsMemsetExternPos 0

private def f3LsMemsetStubAddr : BitVec 64 :=
  (lsPlacedStubPairs.getD lsMemsetExternPos ("", 0#64)).2

private def checkMemsetPinAux (pos : Nat) : Bool :=
  let idx := lsSharedExterns.getD pos 0
  let pair := lsPlacedStubPairs.getD pos ("", 0#64)
  Nat.blt pos lsSharedExterns.length &&
  (pair.1 == "memset") &&
  (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none) &&
  !(f3StdLayout.libcStartMainStage2Addr + 56#64 == pair.2)

set_option maxRecDepth 200000 in
private theorem f3Memset_pin_ok : checkMemsetPinAux lsMemsetExternPos = true := by
  rfl_kernel

private theorem f3Memset_pin_parts :
    lsMemsetExternPos < lsSharedExterns.length ∧
    (lsPlacedStubPairs.getD lsMemsetExternPos ("", 0#64)).1 = "memset" ∧
    Obj.Interned.lookupBlockSymId lsMemsetIdx lsInternedMultiLib.blocks = none ∧
    f3StdLayout.libcStartMainStage2Addr + 56#64 ≠ f3LsMemsetStubAddr := by
  have hc :
      (Nat.blt lsMemsetExternPos lsSharedExterns.length &&
       ((lsPlacedStubPairs.getD lsMemsetExternPos ("", 0#64)).1 == "memset") &&
       (Obj.Interned.lookupBlockSymId lsMemsetIdx lsInternedMultiLib.blocks == none) &&
       !(f3StdLayout.libcStartMainStage2Addr + 56#64 == f3LsMemsetStubAddr)) = true :=
    f3Memset_pin_ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, beq_iff_eq,
    beq_eq_false_iff_ne] at hc
  exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

private theorem lsMemsetIdx_def :
    lsMemsetIdx = lsSharedExterns.getD lsMemsetExternPos 0 := rfl

private theorem f3LsMemsetStubAddr_def :
    f3LsMemsetStubAddr = (lsPlacedStubPairs.getD lsMemsetExternPos ("", 0#64)).2 := rfl

attribute [local irreducible] lsMemsetExternPos lsMemsetIdx f3LsMemsetStubAddr

private theorem lsMemsetExternPos_lt : lsMemsetExternPos < lsSharedExterns.length :=
  f3Memset_pin_parts.1

private theorem lsMemsetStubPair_fst :
    (lsPlacedStubPairs.getD lsMemsetExternPos ("", 0#64)).1 = "memset" :=
  f3Memset_pin_parts.2.1

private theorem lsMemsetIdx_eq_getElem :
    lsMemsetIdx = lsSharedExterns[lsMemsetExternPos]'lsMemsetExternPos_lt := by
  rw [lsMemsetIdx_def]
  exact Obj.Interned.getD_of_lt lsMemsetExternPos_lt

private theorem lsMemsetIdx_lt : lsMemsetIdx < lsInternedMultiLib.names.length := by
  have hmem : lsMemsetIdx ∈ lsSharedExterns := by
    rw [lsMemsetIdx_eq_getElem]
    exact List.getElem_mem lsMemsetExternPos_lt
  exact Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt lsMemsetIdx hmem)

private theorem lsMemsetStubPair_eq :
    lsPlacedStubPairs.getD lsMemsetExternPos ("", 0#64) =
      (lsInternedMultiLib.names.getD lsMemsetIdx "", f3LsSymAddrs.getD lsMemsetIdx 0#64) := by
  have hplen : lsMemsetExternPos < lsPlacedStubPairs.length := by
    rw [lsPlacedStubPairs_eq, List.length_map]
    exact lsMemsetExternPos_lt
  rw [Obj.Interned.getD_of_lt hplen]
  simp only [lsPlacedStubPairs_eq, List.getElem_map, ← lsMemsetIdx_eq_getElem]

private theorem lsMemsetIdx_name :
    lsInternedMultiLib.names.getD lsMemsetIdx "" = "memset" := by
  have hfst := congrArg Prod.fst lsMemsetStubPair_eq
  exact hfst.symm.trans lsMemsetStubPair_fst

private theorem f3LsSymAddrs_memset_eq :
    f3LsSymAddrs.getD lsMemsetIdx 0#64 = f3LsMemsetStubAddr := by
  rw [f3LsMemsetStubAddr_def]
  exact (congrArg Prod.snd lsMemsetStubPair_eq).symm

private theorem lsMemsetIdx_lookupBlockSymId_none :
    Obj.Interned.lookupBlockSymId lsMemsetIdx lsInternedMultiLib.blocks = none :=
  f3Memset_pin_parts.2.2.1

private theorem ls_idxOf_memset :
    lsInternedMultiLib.names.idxOf "memset" = lsMemsetIdx := by
  rw [← lsMemsetIdx_name]
  exact Obj.Interned.idxOf_getD ls_names_nodup lsMemsetIdx_lt

private theorem toMultiPlacement_rho_eq (mly : Obj.Interned.MultiLayout) (names : List String)
    (s : String) :
    (mly.toMultiPlacement names).ρ s = mly.addrs.getD (names.idxOf s) 0#64 := by
  rfl

private theorem f3LsMpl_rho_memset :
    f3LsMpl.ρ "memset" = f3LsMemsetStubAddr := by
  have h1 : f3LsMpl.ρ "memset" = f3LsSymAddrs.getD lsMemsetIdx 0#64 := by
    unfold f3LsMpl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsMpl
    rw [toMultiPlacement_rho_eq, ls_idxOf_memset]
    rfl
  exact h1.trans f3LsSymAddrs_memset_eq

theorem ls_memset_mem_names : "memset" ∈ lsInternedMultiLib.names := by
  rw [← lsMemsetIdx_name, Obj.Interned.getD_of_lt lsMemsetIdx_lt]
  exact List.getElem_mem lsMemsetIdx_lt

theorem ls_memset_lookupBlockSym_none :
    Obj.lookupBlockSym "memset" libsignalSessionLib.blocks = none := by
  rw [← lsMemsetIdx_name, ls_toMultiPlacedLib_eq,
    Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk lsMemsetIdx_lt]
  exact lsMemsetIdx_lookupBlockSymId_none

/-- `"memset"` is an external symbol of `libsignalSessionLib`, so `resolve mpl "memset" = mpl.ρ "memset"`. -/
theorem ls_resolve_memset (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl "memset" = mpl.ρ "memset" := by
  unfold Obj.MultiPlacedLib.resolve
  rw [ls_memset_lookupBlockSym_none]

/-- Relocation-inversion uniqueness pins `mpl.ρ "memset"` to `f3LsMpl.ρ "memset"` for every `mpl`
    satisfying `libsignalSessionLib.LinkedAt cliElfBytes mpl`. -/
theorem f3CliElf_libsignal_memset_rho_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    mpl.ρ "memset" = f3LsMpl.ρ "memset" :=
  (f3CliElf_libsignal_linkedAt_unique hLs).2.2.1 "memset"
    ls_memset_mem_names ls_memset_lookupBlockSym_none

/-- Relocation-inversion uniqueness pins `mmpl.base 21` (`mallocng` `memset`) to
    `f3MallocngMpl.base 21` for every `mmpl` satisfying `mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem f3CliElf_mallocng_base21_eq {mmpl : Obj.MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mmpl.base 21 = f3MallocngMpl.base 21 := by
  have h21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  exact (f3CliElf_mallocng_linkedAt_unique hMm).1 21 h21

private def lsMemcpyExternPos : Nat :=
  findStubPosAux "memcpy" lsPlacedStubPairs 0

private def lsMemcpyIdx : Nat :=
  lsSharedExterns.getD lsMemcpyExternPos 0

private def f3LsMemcpyStubAddr : BitVec 64 :=
  (lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64)).2

private def checkMemcpyPinAux (pos : Nat) : Bool :=
  let idx := lsSharedExterns.getD pos 0
  let pair := lsPlacedStubPairs.getD pos ("", 0#64)
  Nat.blt pos lsSharedExterns.length &&
  (pair.1 == "memcpy") &&
  (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none) &&
  !(f3StdLayout.libcStartMainStage2Addr + 56#64 == pair.2)

set_option maxRecDepth 200000 in
private theorem f3Memcpy_pin_ok : checkMemcpyPinAux lsMemcpyExternPos = true := by
  rfl_kernel

private theorem f3Memcpy_pin_parts :
    lsMemcpyExternPos < lsSharedExterns.length ∧
    (lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64)).1 = "memcpy" ∧
    Obj.Interned.lookupBlockSymId lsMemcpyIdx lsInternedMultiLib.blocks = none ∧
    f3StdLayout.libcStartMainStage2Addr + 56#64 ≠ f3LsMemcpyStubAddr := by
  have hc :
      (Nat.blt lsMemcpyExternPos lsSharedExterns.length &&
       ((lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64)).1 == "memcpy") &&
       (Obj.Interned.lookupBlockSymId lsMemcpyIdx lsInternedMultiLib.blocks == none) &&
       !(f3StdLayout.libcStartMainStage2Addr + 56#64 == f3LsMemcpyStubAddr)) = true :=
    f3Memcpy_pin_ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, beq_iff_eq,
    beq_eq_false_iff_ne] at hc
  exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

private theorem lsMemcpyIdx_def :
    lsMemcpyIdx = lsSharedExterns.getD lsMemcpyExternPos 0 := rfl

private theorem f3LsMemcpyStubAddr_def :
    f3LsMemcpyStubAddr = (lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64)).2 := rfl

attribute [local irreducible] lsMemcpyExternPos lsMemcpyIdx f3LsMemcpyStubAddr

private theorem lsMemcpyExternPos_lt : lsMemcpyExternPos < lsSharedExterns.length :=
  f3Memcpy_pin_parts.1

private theorem lsMemcpyStubPair_fst :
    (lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64)).1 = "memcpy" :=
  f3Memcpy_pin_parts.2.1

private theorem lsMemcpyIdx_eq_getElem :
    lsMemcpyIdx = lsSharedExterns[lsMemcpyExternPos]'lsMemcpyExternPos_lt := by
  rw [lsMemcpyIdx_def]
  exact Obj.Interned.getD_of_lt lsMemcpyExternPos_lt

private theorem lsMemcpyIdx_lt : lsMemcpyIdx < lsInternedMultiLib.names.length := by
  have hmem : lsMemcpyIdx ∈ lsSharedExterns := by
    rw [lsMemcpyIdx_eq_getElem]
    exact List.getElem_mem lsMemcpyExternPos_lt
  exact Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt lsMemcpyIdx hmem)

private theorem lsMemcpyStubPair_eq :
    lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64) =
      (lsInternedMultiLib.names.getD lsMemcpyIdx "", f3LsSymAddrs.getD lsMemcpyIdx 0#64) := by
  have hplen : lsMemcpyExternPos < lsPlacedStubPairs.length := by
    rw [lsPlacedStubPairs_eq, List.length_map]
    exact lsMemcpyExternPos_lt
  rw [Obj.Interned.getD_of_lt hplen]
  simp only [lsPlacedStubPairs_eq, List.getElem_map, ← lsMemcpyIdx_eq_getElem]

private theorem lsMemcpyIdx_name :
    lsInternedMultiLib.names.getD lsMemcpyIdx "" = "memcpy" := by
  have hfst := congrArg Prod.fst lsMemcpyStubPair_eq
  exact hfst.symm.trans lsMemcpyStubPair_fst

private theorem f3LsSymAddrs_memcpy_eq :
    f3LsSymAddrs.getD lsMemcpyIdx 0#64 = f3LsMemcpyStubAddr := by
  rw [f3LsMemcpyStubAddr_def]
  exact (congrArg Prod.snd lsMemcpyStubPair_eq).symm

private theorem lsMemcpyIdx_lookupBlockSymId_none :
    Obj.Interned.lookupBlockSymId lsMemcpyIdx lsInternedMultiLib.blocks = none :=
  f3Memcpy_pin_parts.2.2.1

private theorem ls_idxOf_memcpy :
    lsInternedMultiLib.names.idxOf "memcpy" = lsMemcpyIdx := by
  rw [← lsMemcpyIdx_name]
  exact Obj.Interned.idxOf_getD ls_names_nodup lsMemcpyIdx_lt

private theorem f3LsMpl_rho_memcpy :
    f3LsMpl.ρ "memcpy" = f3LsMemcpyStubAddr := by
  have h1 : f3LsMpl.ρ "memcpy" = f3LsSymAddrs.getD lsMemcpyIdx 0#64 := by
    unfold f3LsMpl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsMpl
    rw [toMultiPlacement_rho_eq, ls_idxOf_memcpy]
    rfl
  exact h1.trans f3LsSymAddrs_memcpy_eq

theorem ls_memcpy_mem_names : "memcpy" ∈ lsInternedMultiLib.names := by
  rw [← lsMemcpyIdx_name, Obj.Interned.getD_of_lt lsMemcpyIdx_lt]
  exact List.getElem_mem lsMemcpyIdx_lt

theorem ls_memcpy_lookupBlockSym_none :
    Obj.lookupBlockSym "memcpy" libsignalSessionLib.blocks = none := by
  rw [← lsMemcpyIdx_name, ls_toMultiPlacedLib_eq,
    Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk lsMemcpyIdx_lt]
  exact lsMemcpyIdx_lookupBlockSymId_none

/-- `"memcpy"` is an external symbol of `libsignalSessionLib`, so `resolve mpl "memcpy" = mpl.ρ "memcpy"`. -/
theorem ls_resolve_memcpy (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl "memcpy" = mpl.ρ "memcpy" := by
  unfold Obj.MultiPlacedLib.resolve
  rw [ls_memcpy_lookupBlockSym_none]

/-- Relocation-inversion uniqueness pins `mpl.ρ "memcpy"` to `f3LsMpl.ρ "memcpy"` for every `mpl`
    satisfying `libsignalSessionLib.LinkedAt cliElfBytes mpl`. -/
theorem f3CliElf_libsignal_memcpy_rho_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    mpl.ρ "memcpy" = f3LsMpl.ρ "memcpy" :=
  (f3CliElf_libsignal_linkedAt_unique hLs).2.2.1 "memcpy"
    ls_memcpy_mem_names ls_memcpy_lookupBlockSym_none

/-- Relocation-inversion uniqueness pins `mmpl.base 20` (`mallocng` `memcpy`, 396 B) to
    `f3MallocngMpl.base 20` for every `mmpl` satisfying `mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem f3CliElf_mallocng_base20_eq {mmpl : Obj.MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mmpl.base 20 = f3MallocngMpl.base 20 := by
  have h20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  exact (f3CliElf_mallocng_linkedAt_unique hMm).1 20 h20

/-! ## 2. Startup `lr` (`f3StdLayout.libcStartMainStage2Addr + 56#64`) `decide` Checks & `LinkedAt` Lift -/

/-- At the pinned `f3MallocngMpl` placement, `f3StdLayout.libcStartMainStage2Addr + 56#64` lies
    outside the 260-byte `memset` block (`blk21`). -/
theorem f3StartupLr_keepMemsetBlk21_f3 :
    keepMemsetBlk21 f3MallocngMpl (f3StdLayout.libcStartMainStage2Addr + 56#64) = false := by
  decide

/-- At the pinned `f3LsMpl` placement, `f3StdLayout.libcStartMainStage2Addr + 56#64` is distinct
    from the `"memset"` stub `f3LsMpl.ρ "memset"`. -/
theorem f3StartupLr_ne_f3LsMemsetStub :
    f3StdLayout.libcStartMainStage2Addr + 56#64 ≠ f3LsMpl.ρ "memset" := by
  rw [f3LsMpl_rho_memset]
  exact f3Memset_pin_parts.2.2.2

/-- Layout-generic `keepMemsetBlk21 mmpl (sm.readReg64 .lr) = false` at startup `lr`. -/
theorem f3StartupLr_keepMemsetBlk21_false
    {mmpl : Obj.MultiPlacement} {sm : State}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    keepMemsetBlk21 mmpl (sm.readReg64 .lr) = false := by
  have hkeq : keepMemsetBlk21 mmpl (sm.readReg64 .lr) =
      keepMemsetBlk21 f3MallocngMpl (f3StdLayout.libcStartMainStage2Addr + 56#64) := by
    unfold keepMemsetBlk21
    rw [hlr, f3CliElf_mallocng_base21_eq hMm]
  exact hkeq.trans f3StartupLr_keepMemsetBlk21_f3

/-- Layout-generic `sm.readReg64 .lr ≠ mpl.ρ "memset"` at startup `lr`. -/
theorem f3StartupLr_ne_memsetStub
    {mpl : Obj.MultiPlacement} {sm : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hlr : sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    sm.readReg64 .lr ≠ mpl.ρ "memset" := by
  rw [hlr, f3CliElf_libsignal_memset_rho_eq hLs]
  exact f3StartupLr_ne_f3LsMemsetStub

/-- **D3 main theorem (`f3MemsetEntryGuard_of_startupLr`):**
    Discharges `F3MemsetEntryGuard mpl mmpl sm` (`= MemsetEntryGuard mmpl (mpl.ρ "memset") sm`)
    layout-generically from `hlr : sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64`
    and the `LinkedAt cliElfBytes` witnesses for `mpl` and `mmpl`. -/
theorem f3MemsetEntryGuard_of_startupLr
    {mpl mmpl : Obj.MultiPlacement} {sm : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    F3MemsetEntryGuard mpl mmpl sm :=
  ⟨f3StartupLr_keepMemsetBlk21_false hMm hlr, f3StartupLr_ne_memsetStub hLs hlr⟩

/-- `libsignalSessionLib.resolve mpl "memset"` form of `f3MemsetEntryGuard_of_startupLr`. -/
theorem memsetEntryGuard_resolve_of_startupLr
    {mpl mmpl : Obj.MultiPlacement} {sm : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    MemsetEntryGuard mmpl (libsignalSessionLib.resolve mpl "memset") sm := by
  rw [ls_resolve_memset]
  exact f3MemsetEntryGuard_of_startupLr hLs hMm hlr

/-- At the pinned `f3MallocngMpl` placement, `f3StdLayout.libcStartMainStage2Addr + 56#64` lies
    outside the 396-byte `memcpy` block (`blk20`). -/
theorem f3StartupLr_keepMemcpyBlk20_f3 :
    keepMemcpyBlk20 f3MallocngMpl (f3StdLayout.libcStartMainStage2Addr + 56#64) = false := by
  decide

/-- At the pinned `f3LsMpl` placement, `f3StdLayout.libcStartMainStage2Addr + 56#64` is distinct
    from the `"memcpy"` stub `f3LsMpl.ρ "memcpy"`. -/
theorem f3StartupLr_ne_f3LsMemcpyStub :
    f3StdLayout.libcStartMainStage2Addr + 56#64 ≠ f3LsMpl.ρ "memcpy" := by
  rw [f3LsMpl_rho_memcpy]
  exact f3Memcpy_pin_parts.2.2.2

/-- Layout-generic `keepMemcpyBlk20 mmpl (sm.readReg64 .lr) = false` at startup `lr`. -/
theorem f3StartupLr_keepMemcpyBlk20_false
    {mmpl : Obj.MultiPlacement} {sm : State}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    keepMemcpyBlk20 mmpl (sm.readReg64 .lr) = false := by
  have hkeq : keepMemcpyBlk20 mmpl (sm.readReg64 .lr) =
      keepMemcpyBlk20 f3MallocngMpl (f3StdLayout.libcStartMainStage2Addr + 56#64) := by
    unfold keepMemcpyBlk20
    rw [hlr, f3CliElf_mallocng_base20_eq hMm]
  exact hkeq.trans f3StartupLr_keepMemcpyBlk20_f3

/-- Layout-generic `sm.readReg64 .lr ≠ mpl.ρ "memcpy"` at startup `lr`. -/
theorem f3StartupLr_ne_memcpyStub
    {mpl : Obj.MultiPlacement} {sm : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hlr : sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    sm.readReg64 .lr ≠ mpl.ρ "memcpy" := by
  rw [hlr, f3CliElf_libsignal_memcpy_rho_eq hLs]
  exact f3StartupLr_ne_f3LsMemcpyStub

/-- Variant-A real-side entry guard for `memcpy` (`blk20`, 396 B) at `stubPc`. -/
@[expose] def MemcpyEntryGuard
    (mmpl : Obj.MultiPlacement) (stubPc : BitVec 64) (s0 : State) : Prop :=
  keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

/-- Specialization of `MemcpyEntryGuard` to `libsignalSessionLib`'s `"memcpy"` stub `mpl.ρ "memcpy"`. -/
@[expose] def F3MemcpyEntryGuard (mpl mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  MemcpyEntryGuard mmpl (mpl.ρ "memcpy") s0

/-- Discharges `F3MemcpyEntryGuard mpl mmpl sm` layout-generically from `StdMainEntryLr f3StdLayout sm`
    and `LinkedAt cliElfBytes` witnesses for `mpl` and `mmpl`. -/
theorem f3MemcpyEntryGuard_of_startupLr
    {mpl mmpl : Obj.MultiPlacement} {sm : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : StdMainEntryLr f3StdLayout sm) :
    F3MemcpyEntryGuard mpl mmpl sm :=
  ⟨f3StartupLr_keepMemcpyBlk20_false hMm hlr, f3StartupLr_ne_memcpyStub hLs hlr⟩

/-- `libsignalSessionLib.resolve mpl "memcpy"` form of `f3MemcpyEntryGuard_of_startupLr`. -/
theorem memcpyEntryGuard_resolve_of_startupLr
    {mpl mmpl : Obj.MultiPlacement} {sm : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : StdMainEntryLr f3StdLayout sm) :
    MemcpyEntryGuard mmpl (libsignalSessionLib.resolve mpl "memcpy") sm := by
  rw [ls_resolve_memcpy]
  exact f3MemcpyEntryGuard_of_startupLr hLs hMm hlr

/-- Combined `W`-independent Block-`617` entry-`lr`-false predicate covering both `memset` (`blk21`)
    and `memcpy` (`blk20`), sufficient for `_of_trap_ret` replays. -/
@[expose] def F3MemsetMemcpyEntryLrFalse (mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧
  keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false

theorem f3MemsetMemcpyEntryLrFalse_iff_keepMemOps_false
    (mmpl : Obj.MultiPlacement) (s0 : State) :
    F3MemsetMemcpyEntryLrFalse mmpl s0 ↔ keepMemOps mmpl (s0.readReg64 .lr) = false := by
  unfold F3MemsetMemcpyEntryLrFalse keepMemOps
  rw [Bool.or_eq_false_iff, and_comm]

/-- Derives `F3MemsetMemcpyEntryLrFalse mmpl sm` from `StdMainEntryLr f3StdLayout sm` and
    `hMm : mallocngLib.LinkedAt cliElfBytes mmpl` (`W`-independent, `mpl`-independent). -/
theorem f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr
    {mmpl : Obj.MultiPlacement} {sm : State}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : StdMainEntryLr f3StdLayout sm) :
    F3MemsetMemcpyEntryLrFalse mmpl sm :=
  ⟨f3StartupLr_keepMemsetBlk21_false hMm hlr, f3StartupLr_keepMemcpyBlk20_false hMm hlr⟩

theorem f3KeepMemOps_false_of_stdMainEntryLr
    {mmpl : Obj.MultiPlacement} {sm : State}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : StdMainEntryLr f3StdLayout sm) :
    keepMemOps mmpl (sm.readReg64 .lr) = false :=
  (f3MemsetMemcpyEntryLrFalse_iff_keepMemOps_false mmpl sm).mp
    (f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr hMm hlr)

theorem f3MemsetAndMemcpyEntryGuard_of_stdMainEntryLr
    {mpl mmpl : Obj.MultiPlacement} {sm : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : StdMainEntryLr f3StdLayout sm) :
    F3MemsetEntryGuard mpl mmpl sm ∧ F3MemcpyEntryGuard mpl mmpl sm :=
  ⟨f3MemsetEntryGuard_of_startupLr hLs hMm hlr, f3MemcpyEntryGuard_of_startupLr hLs hMm hlr⟩

/-! ## 3. `W`-Independent Guarded-Harness Corollaries (`StartupStatics` → Entry Guards) -/

/-- `W`-independent `keepMemsetBlk21 mmpl (sm.readReg64 .lr) = false` guarded harness corollary. -/
theorem cliElf_f3MuslHarness_memsetLrFalse_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      (patchElfTokensPlacedAt mpl cliElfImage)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (mpl.base 617) cliProcessInputs mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl)
      (fun sm => keepMemsetBlk21 mmpl (sm.readReg64 .lr) = false) :=
  (cliElf_f3MuslHarnessLr_of_linkedAt hls hmng W).mono_guard
    (fun _ hlr => f3StartupLr_keepMemsetBlk21_false hmng hlr)

/-- `W`-independent `keepMemcpyBlk20 mmpl (sm.readReg64 .lr) = false` guarded harness corollary. -/
theorem cliElf_f3MuslHarness_memcpyLrFalse_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      (patchElfTokensPlacedAt mpl cliElfImage)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (mpl.base 617) cliProcessInputs mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl)
      (fun sm => keepMemcpyBlk20 mmpl (sm.readReg64 .lr) = false) :=
  (cliElf_f3MuslHarnessLr_of_linkedAt hls hmng W).mono_guard
    (fun _ hlr => f3StartupLr_keepMemcpyBlk20_false hmng hlr)

/-- `W`-independent `F3MemsetMemcpyEntryLrFalse mmpl` guarded harness directly from
    `StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt`. -/
theorem cliElf_f3MuslHarness_memsetMemcpyLrFalse_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      (patchElfTokensPlacedAt mpl cliElfImage)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (mpl.base 617) cliProcessInputs mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl)
      (F3MemsetMemcpyEntryLrFalse mmpl) :=
  (cliElf_f3MuslHarnessLr_of_linkedAt hls hmng W).mono_guard
    (fun _ hlr => f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr hmng hlr)

/-- `W`-independent `keepMemOps mmpl (sm.readReg64 .lr) = false` guarded harness corollary. -/
theorem cliElf_f3MuslHarness_keepMemOpsFalse_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      (patchElfTokensPlacedAt mpl cliElfImage)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (mpl.base 617) cliProcessInputs mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl)
      (fun sm => keepMemOps mmpl (sm.readReg64 .lr) = false) :=
  (cliElf_f3MuslHarnessLr_of_linkedAt hls hmng W).mono_guard
    (fun _ hlr => f3KeepMemOps_false_of_stdMainEntryLr hmng hlr)

/-- `W`-independent `F3MemsetEntryGuard mpl mmpl` guarded harness corollary. -/
theorem cliElf_f3MuslHarness_memsetEntryGuard_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      (patchElfTokensPlacedAt mpl cliElfImage)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (mpl.base 617) cliProcessInputs mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl)
      (F3MemsetEntryGuard mpl mmpl) :=
  (cliElf_f3MuslHarnessLr_of_linkedAt hls hmng W).mono_guard
    (fun _ hlr => f3MemsetEntryGuard_of_startupLr hls hmng hlr)

/-- `W`-independent `F3MemcpyEntryGuard mpl mmpl` guarded harness corollary. -/
theorem cliElf_f3MuslHarness_memcpyEntryGuard_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      (patchElfTokensPlacedAt mpl cliElfImage)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (mpl.base 617) cliProcessInputs mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl)
      (F3MemcpyEntryGuard mpl mmpl) :=
  (cliElf_f3MuslHarnessLr_of_linkedAt hls hmng W).mono_guard
    (fun _ hlr => f3MemcpyEntryGuard_of_startupLr hls hmng hlr)

/-- `W`-independent combined `F3MemsetEntryGuard ∧ F3MemcpyEntryGuard` guarded harness corollary. -/
theorem cliElf_f3MuslHarness_memsetAndMemcpyEntryGuard_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      (patchElfTokensPlacedAt mpl cliElfImage)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (mpl.base 617) cliProcessInputs mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl)
      (fun sm => F3MemsetEntryGuard mpl mmpl sm ∧ F3MemcpyEntryGuard mpl mmpl sm) :=
  (cliElf_f3MuslHarnessLr_of_linkedAt hls hmng W).mono_guard
    (fun _ hlr => f3MemsetAndMemcpyEntryGuard_of_stdMainEntryLr hls hmng hlr)

/-! ## 4. `Block617TransferFixedHypG` Instances via `block617TransferFixedG_of_replaysOn_outcome` -/

/-- **General K-pass-ready `F3CodeOk` / `F3MemsetMemcpyEntryLrFalse` transfer over arbitrary `keep`
    (`f3Block617TransferFixedG_of_entryLrFalse_outcome_keep`):**
    Instantiates `block617TransferFixedG_of_replaysOn_outcome` on `InvMem := F3CodeInv mpl mmpl`
    and `CodeOk_ghost := CodeOk_real := F3CodeOk mpl mmpl` for any `keep : BitVec 64 → Bool`
    (e.g. `hole2_keepSub mpl mmpl` for a 1-pass K-arm CLI cutover, or `fun _ => false` for a
    2-pass memory-ops cutover), forwarding `sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false`,
    `sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false`, `∀ msg, sf.status ≠ .Exception msg`,
    and `sf.status ≠ .Halted` from `subroutineOutcome_running_pc_and_noFault`. -/
theorem f3Block617TransferFixedG_of_entryLrFalse_outcome_keep
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (keep : BitVec 64 → Bool)
    (PredFs : FsState → Prop)
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hReplay : ∀ (W : CliHooks) (s0 sf : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real := cliProgExtPlacedAt mpl ER 617 W
      F3CodeOk mpl mmpl s0.mem →
      Steps P_ghost s0 sf →
      (sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false) →
      (sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false) →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      GhostExternReplaysOn keep (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
        P_ghost P_real s0 sf)
    (hSvcFs : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → F3CodeInv mpl mmpl z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs)
    (hlr_calls : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real := cliProgExtPlacedAt mpl ER 617 W
      F3CodeOk mpl mmpl s0.mem →
      Steps P_ghost s0 z → Steps P_ghost z sf →
      z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false) :
    Block617TransferFixedHypG mpl mmpl EG ER (F3MemsetMemcpyEntryLrFalse mmpl)
      (F3CodeOk mpl mmpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk := by
  refine block617TransferFixedG_of_replaysOn_outcome keep (F3CodeInv mpl mmpl) PredFs
    hNoNewHooks
    (fun _ h => h)
    (fun W _ hCO => codeLoaded_cliProgExtPlaced_of_codeRoLoaded W hCO.1.lsRo)
    (fun _ hCO => hCO.2)
    (fun _ hCO => hCO.1)
    (fun _ _ hInv hkf => hInv.of_keepsFrozen hkf)
    hFs0 fun W _Run _γ _tp _g _R s0 sf hGuard hCO _hpc _hfs _htr hSteps hout => ?_
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  have hrun_blk21 : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false :=
    fun hrun => hret_pc hrun ▸ hGuard.1
  have hrun_blk20 : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false :=
    fun hrun => hret_pc hrun ▸ hGuard.2
  exact ⟨hReplay W s0 sf hCO hSteps hrun_blk21 hrun_blk20 hnoex_sf hnhalt_sf,
    fun z hs1 hs2 hrun_z hext_z hfetch_z hfr_z hinv_z hfs_z =>
      hSvcFs W s0 sf z hs1 hs2 hrun_z hext_z hfetch_z hfr_z hinv_z hfs_z,
    fun z hs1 hs2 hrun_z hne => hlr_calls W s0 sf z hCO hs1 hs2 hrun_z hne⟩

/-- `StdMainEntryLr f3StdLayout` specialization of
    `f3Block617TransferFixedG_of_entryLrFalse_outcome_keep`. -/
theorem f3Block617TransferFixedG_of_stdMainEntryLr_outcome_keep
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (keep : BitVec 64 → Bool)
    (PredFs : FsState → Prop)
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hReplay : ∀ (W : CliHooks) (s0 sf : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real := cliProgExtPlacedAt mpl ER 617 W
      F3CodeOk mpl mmpl s0.mem →
      Steps P_ghost s0 sf →
      (sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false) →
      (sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false) →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      GhostExternReplaysOn keep (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
        P_ghost P_real s0 sf)
    (hSvcFs : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → F3CodeInv mpl mmpl z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs)
    (hlr_calls : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real := cliProgExtPlacedAt mpl ER 617 W
      F3CodeOk mpl mmpl s0.mem →
      Steps P_ghost s0 z → Steps P_ghost z sf →
      z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false) :
    Block617TransferFixedHypG mpl mmpl EG ER (StdMainEntryLr f3StdLayout)
      (F3CodeOk mpl mmpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk :=
  (f3Block617TransferFixedG_of_entryLrFalse_outcome_keep keep PredFs hNoNewHooks hFs0 hReplay
    hSvcFs hlr_calls).mono_guard
    (fun _ hlr => f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr hMm hlr)

/-- **`keep := fun _ => false` specialization (`f3Block617TransferFixedG_of_entryLrFalse_outcome`):**
    Closes `hlr_calls` automatically by `rfl` when every mismatched hook discharges its own `lr`
    obligation internally via `_of_trap_ret`. -/
theorem f3Block617TransferFixedG_of_entryLrFalse_outcome
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (PredFs : FsState → Prop)
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hReplay : ∀ (W : CliHooks) (s0 sf : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real := cliProgExtPlacedAt mpl ER 617 W
      F3CodeOk mpl mmpl s0.mem →
      Steps P_ghost s0 sf →
      (sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false) →
      (sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false) →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      GhostExternReplaysOn (fun _ => false) (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
        P_ghost P_real s0 sf)
    (hSvcFs : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → F3CodeInv mpl mmpl z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs) :
    Block617TransferFixedHypG mpl mmpl EG ER (F3MemsetMemcpyEntryLrFalse mmpl)
      (F3CodeOk mpl mmpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk :=
  f3Block617TransferFixedG_of_entryLrFalse_outcome_keep (fun _ => false) PredFs hNoNewHooks hFs0
    hReplay hSvcFs (fun _ _ _ _ _ _ _ _ _ => rfl)

/-- `StdMainEntryLr f3StdLayout` specialization of `f3Block617TransferFixedG_of_entryLrFalse_outcome`
    under `hMm : mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem f3Block617TransferFixedG_of_stdMainEntryLr_outcome
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (PredFs : FsState → Prop)
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hReplay : ∀ (W : CliHooks) (s0 sf : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real := cliProgExtPlacedAt mpl ER 617 W
      F3CodeOk mpl mmpl s0.mem →
      Steps P_ghost s0 sf →
      (sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false) →
      (sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false) →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      GhostExternReplaysOn (fun _ => false) (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
        P_ghost P_real s0 sf)
    (hSvcFs : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → F3CodeInv mpl mmpl z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs) :
    Block617TransferFixedHypG mpl mmpl EG ER (StdMainEntryLr f3StdLayout)
      (F3CodeOk mpl mmpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk :=
  (f3Block617TransferFixedG_of_entryLrFalse_outcome PredFs hNoNewHooks hFs0 hReplay hSvcFs).mono_guard
    (fun _ hlr => f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr hMm hlr)

/-- **Concrete `memset`-only narrow-ghost `Block617TransferFixedHypG` instance via
    `block617TransferFixedG_of_replaysOn_outcome` (`f3Block617TransferFixedG_memset_of_replaysOn_outcome`):**
    Discharges `memsetGhostHookBlk21 (keepMemsetBlk21 mmpl)` at `mpl.ρ "memset"` under
    `Guard := fun s0 => keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false` (`0` `PlacedInst` / WP4
    imports). Note (`rev_c6` F2 / `rev_c8` T2): `hother` equates `EG` and `ER` outside `memset`
    (single-mismatch pass, e.g. Pass 1 of a 2-pass cutover; for the 1-pass K CLI cutover use
    `f3Block617TransferFixedG_of_entryLrFalse_outcome_keep`). -/
theorem f3Block617TransferFixedG_memset_of_replaysOn_outcome
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (PredFs : FsState → Prop)
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hghost_ms : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (mpl.ρ "memset") =
        some (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) (cliProgExtPlacedAt mpl ER 617 W) mmpl))
    (hother : ∀ (W : CliHooks) (pc : BitVec 64),
      pc ≠ mpl.ρ "memset" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc =
        (cliProgExtPlacedAt mpl ER 617 W).externAt? pc)
    (hreal_ms_none : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt? (mpl.ρ "memset") = none)
    (hreal_blk21_none : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hblk21_ext : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hStub_ms : ∀ W : CliHooks,
      StubReachesTargetOn (F3CodeInv mpl mmpl) (cliProgExtPlacedAt mpl ER 617 W)
        (mpl.ρ "memset") (mmpl.base 21))
    (hRealHooks : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → F3CodeInv mpl mmpl u.mem → PredFs u.fs →
        ExecFrozen (f u).mem ∧ PredFs (f u).fs)
    (hSvcFs : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → F3CodeInv mpl mmpl z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs) :
    Block617TransferFixedHypG mpl mmpl EG ER
      (fun s0 => keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false)
      (F3CodeOk mpl mmpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk := by
  have hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none := by
    intro W pc hgn
    by_cases hms : pc = mpl.ρ "memset"
    · subst hms; exact hreal_ms_none W
    · rw [← hother W pc hms]; exact hgn
  have hmng21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  refine block617TransferFixedG_of_replaysOn_outcome (fun _ => false) (F3CodeInv mpl mmpl) PredFs
    hNoNewHooks
    (fun _ h => h)
    (fun W _ hCO => codeLoaded_cliProgExtPlaced_of_codeRoLoaded W hCO.1.lsRo)
    (fun _ hCO => hCO.2)
    (fun _ hCO => hCO.1)
    (fun _ _ hInv hkf => hInv.of_keepsFrozen hkf)
    hFs0 fun W _Run _γ _tp _g _R s0 sf hGuard _hCO _hpc _hfs _htr _hSteps hout => ?_
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  have hrun_blk21 : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false :=
    fun hrun => hret_pc hrun ▸ hGuard
  refine ⟨?_,
    fun z hs1 hs2 hrun_z hext_z hfetch_z hfr_z hinv_z hfs_z =>
      hSvcFs W s0 sf z hs1 hs2 hrun_z hext_z hfetch_z hfr_z hinv_z hfs_z,
    fun _ _ _ _ _ => rfl⟩
  intro pc f hge
  by_cases hms : pc = mpl.ρ "memset"
  · subst hms
    rw [hghost_ms W] at hge
    injection hge with hf; subst hf
    have hRep := ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret
      (InvMem := F3CodeInv mpl mmpl)
      (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
      (P_real := cliProgExtPlacedAt mpl ER 617 W)
      (mmpl := mmpl) (stubPc := mpl.ρ "memset")
      (hblk21_ext W) rfl (hreal_blk21_none W) (hreal_ms_none W) (hStub_ms W)
      (fun m _ hinv => hinv.mngBlockCodeLoaded 21 hmng21 _ _ Syscall.standard)
      (fun _ _ hinv hkf => hinv.of_keepsFrozen hkf)
      hrun_blk21 hnoex_sf hnhalt_sf
    refine Or.inr ⟨hRep.1, fun u _hs0 hrest hpc hrun hnoex hkf hfr _hlr ⟨hinv, hfs_u⟩ => ?_⟩
    obtain ⟨hsteps_r, hfr', hinv'⟩ := hRep.2 u hrest hpc hrun hnoex hkf hfr hinv
    have hfs_eq : (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl)
        (cliProgExtPlacedAt mpl ER 617 W) mmpl u).fs = u.fs :=
      memsetGhostHook_fs _ _ _ _ u
    exact ⟨hsteps_r, hfr', hinv', hfs_eq ▸ hfs_u⟩
  · have hre : (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = some f := by
      rw [← hother W pc hms]; exact hge
    refine Or.inl ⟨hre, fun u _ _ _ hrun _ hkf hfr ⟨hinv, hfs_u⟩ => ?_⟩
    obtain ⟨hfr', hfs'⟩ := hRealHooks W pc f hre u hrun hfr hinv hfs_u
    exact ⟨hfr', hinv.of_keepsFrozen hkf, hfs'⟩

/-- `StdMainEntryLr f3StdLayout` specialization of
    `f3Block617TransferFixedG_memset_of_replaysOn_outcome` under
    `hMm : mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem f3Block617TransferFixedG_memset_of_stdMainEntryLr
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (PredFs : FsState → Prop)
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hghost_ms : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (mpl.ρ "memset") =
        some (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) (cliProgExtPlacedAt mpl ER 617 W) mmpl))
    (hother : ∀ (W : CliHooks) (pc : BitVec 64),
      pc ≠ mpl.ρ "memset" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc =
        (cliProgExtPlacedAt mpl ER 617 W).externAt? pc)
    (hreal_ms_none : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt? (mpl.ρ "memset") = none)
    (hreal_blk21_none : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hblk21_ext : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hStub_ms : ∀ W : CliHooks,
      StubReachesTargetOn (F3CodeInv mpl mmpl) (cliProgExtPlacedAt mpl ER 617 W)
        (mpl.ρ "memset") (mmpl.base 21))
    (hRealHooks : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → F3CodeInv mpl mmpl u.mem → PredFs u.fs →
        ExecFrozen (f u).mem ∧ PredFs (f u).fs)
    (hSvcFs : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → F3CodeInv mpl mmpl z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs) :
    Block617TransferFixedHypG mpl mmpl EG ER (StdMainEntryLr f3StdLayout)
      (F3CodeOk mpl mmpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk :=
  (f3Block617TransferFixedG_memset_of_replaysOn_outcome PredFs hFs0 hghost_ms hother hreal_ms_none
    hreal_blk21_none hblk21_ext hStub_ms hRealHooks hSvcFs).mono_guard
    (fun _ hlr => f3StartupLr_keepMemsetBlk21_false hMm hlr)

/-- **Concrete `memset` + `memcpy` narrow-ghost `Block617TransferFixedHypG` instance via
    `block617TransferFixedG_of_replaysOn_outcome` (`f3Block617TransferFixedG_memsetMemcpy_of_replaysOn_outcome`):**
    Simultaneously discharges narrow `memset` (`memsetGhostHookBlk21 (keepMemsetBlk21 mmpl)`) at
    `mpl.ρ "memset"` and narrow `memcpy` (`memcpyGhostHookBlk20 (keepMemcpyBlk20 mmpl)`) at
    `mpl.ρ "memcpy"` on `(F3CodeOk mpl mmpl, F3MemsetMemcpyEntryLrFalse mmpl)` with `0` `PlacedInst`
    or WP4 imports. Note (`rev_c6` F2 / `rev_c8` T2): `hother` equates `EG` and `ER` outside
    `memset`/`memcpy` (2-mismatch pass; for the 1-pass K CLI cutover use
    `f3Block617TransferFixedG_of_entryLrFalse_outcome_keep`). -/
theorem f3Block617TransferFixedG_memsetMemcpy_of_replaysOn_outcome
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (PredFs : FsState → Prop)
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hghost_ms : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (mpl.ρ "memset") =
        some (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) (cliProgExtPlacedAt mpl ER 617 W) mmpl))
    (hghost_mc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (mpl.ρ "memcpy") =
        some (memcpyGhostHookBlk20 (keepMemcpyBlk20 mmpl) (cliProgExtPlacedAt mpl ER 617 W) mmpl))
    (hother : ∀ (W : CliHooks) (pc : BitVec 64),
      pc ≠ mpl.ρ "memset" → pc ≠ mpl.ρ "memcpy" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc =
        (cliProgExtPlacedAt mpl ER 617 W).externAt? pc)
    (hreal_ms_none : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt? (mpl.ρ "memset") = none)
    (hreal_mc_none : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt? (mpl.ρ "memcpy") = none)
    (hreal_blk21_none : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hreal_blk20_none : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hblk21_ext : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hblk20_ext : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hStub_ms : ∀ W : CliHooks,
      StubReachesTargetOn (F3CodeInv mpl mmpl) (cliProgExtPlacedAt mpl ER 617 W)
        (mpl.ρ "memset") (mmpl.base 21))
    (hStub_mc : ∀ W : CliHooks,
      StubReachesTargetOn (F3CodeInv mpl mmpl) (cliProgExtPlacedAt mpl ER 617 W)
        (mpl.ρ "memcpy") (mmpl.base 20))
    (hRealHooks : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → F3CodeInv mpl mmpl u.mem → PredFs u.fs →
        ExecFrozen (f u).mem ∧ PredFs (f u).fs)
    (hSvcFs : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → F3CodeInv mpl mmpl z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs) :
    Block617TransferFixedHypG mpl mmpl EG ER (F3MemsetMemcpyEntryLrFalse mmpl)
      (F3CodeOk mpl mmpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk := by
  have hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none := by
    intro W pc hgn
    by_cases hms : pc = mpl.ρ "memset"
    · subst hms; exact hreal_ms_none W
    · by_cases hmc : pc = mpl.ρ "memcpy"
      · subst hmc; exact hreal_mc_none W
      · rw [← hother W pc hms hmc]; exact hgn
  have hmng20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  have hmng21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  refine f3Block617TransferFixedG_of_entryLrFalse_outcome PredFs hNoNewHooks hFs0
    (fun W s0 sf _hCO _hSteps hrun_blk21 hrun_blk20 hnoex_sf hnhalt_sf pc f hge => ?_) hSvcFs
  by_cases hms : pc = mpl.ρ "memset"
  · subst hms
    rw [hghost_ms W] at hge
    injection hge with hf; subst hf
    have hRep := ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret
      (InvMem := F3CodeInv mpl mmpl)
      (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
      (P_real := cliProgExtPlacedAt mpl ER 617 W)
      (mmpl := mmpl) (stubPc := mpl.ρ "memset")
      (hblk21_ext W) rfl (hreal_blk21_none W) (hreal_ms_none W) (hStub_ms W)
      (fun m _ hinv => hinv.mngBlockCodeLoaded 21 hmng21 _ _ Syscall.standard)
      (fun _ _ hinv hkf => hinv.of_keepsFrozen hkf)
      hrun_blk21 hnoex_sf hnhalt_sf
    refine Or.inr ⟨hRep.1, fun u _hs0 hrest hpc hrun hnoex hkf hfr _hlr ⟨hinv, hfs_u⟩ => ?_⟩
    obtain ⟨hsteps_r, hfr', hinv'⟩ := hRep.2 u hrest hpc hrun hnoex hkf hfr hinv
    have hfs_eq : (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl)
        (cliProgExtPlacedAt mpl ER 617 W) mmpl u).fs = u.fs :=
      memsetGhostHook_fs _ _ _ _ u
    exact ⟨hsteps_r, hfr', hinv', hfs_eq ▸ hfs_u⟩
  · by_cases hmc : pc = mpl.ρ "memcpy"
    · subst hmc
      rw [hghost_mc W] at hge
      injection hge with hf; subst hf
      have hRep := ghostExternReplaysOn_memcpyGhostHookNarrow_of_trap_ret
        (InvMem := F3CodeInv mpl mmpl)
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_real := cliProgExtPlacedAt mpl ER 617 W)
        (mmpl := mmpl) (stubPc := mpl.ρ "memcpy")
        (hblk20_ext W) rfl (hreal_blk20_none W) (hreal_mc_none W) (hStub_mc W)
        (fun m _ hinv => hinv.mngBlockCodeLoaded 20 hmng20 _ _ Syscall.standard)
        (fun _ _ hinv hkf => hinv.of_keepsFrozen hkf)
        hrun_blk20 hnoex_sf hnhalt_sf
      refine Or.inr ⟨hRep.1, fun u _hs0 hrest hpc hrun hnoex hkf hfr _hlr ⟨hinv, hfs_u⟩ => ?_⟩
      obtain ⟨hsteps_r, hfr', hinv'⟩ := hRep.2 u hrest hpc hrun hnoex hkf hfr hinv
      have hfs_eq : (memcpyGhostHookBlk20 (keepMemcpyBlk20 mmpl)
          (cliProgExtPlacedAt mpl ER 617 W) mmpl u).fs = u.fs :=
        memcpyGhostHook_fs _ _ _ _ u
      exact ⟨hsteps_r, hfr', hinv', hfs_eq ▸ hfs_u⟩
    · have hre : (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = some f := by
        rw [← hother W pc hms hmc]; exact hge
      refine Or.inl ⟨hre, fun u _ _ _ hrun _ hkf hfr ⟨hinv, hfs_u⟩ => ?_⟩
      obtain ⟨hfr', hfs'⟩ := hRealHooks W pc f hre u hrun hfr hinv hfs_u
      exact ⟨hfr', hinv.of_keepsFrozen hkf, hfs'⟩

/-- `StdMainEntryLr f3StdLayout` specialization of
    `f3Block617TransferFixedG_memsetMemcpy_of_replaysOn_outcome` under
    `hMm : mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem f3Block617TransferFixedG_memsetMemcpy_of_stdMainEntryLr
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (PredFs : FsState → Prop)
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hghost_ms : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (mpl.ρ "memset") =
        some (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) (cliProgExtPlacedAt mpl ER 617 W) mmpl))
    (hghost_mc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (mpl.ρ "memcpy") =
        some (memcpyGhostHookBlk20 (keepMemcpyBlk20 mmpl) (cliProgExtPlacedAt mpl ER 617 W) mmpl))
    (hother : ∀ (W : CliHooks) (pc : BitVec 64),
      pc ≠ mpl.ρ "memset" → pc ≠ mpl.ρ "memcpy" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc =
        (cliProgExtPlacedAt mpl ER 617 W).externAt? pc)
    (hreal_ms_none : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt? (mpl.ρ "memset") = none)
    (hreal_mc_none : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt? (mpl.ρ "memcpy") = none)
    (hreal_blk21_none : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hreal_blk20_none : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hblk21_ext : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hblk20_ext : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hStub_ms : ∀ W : CliHooks,
      StubReachesTargetOn (F3CodeInv mpl mmpl) (cliProgExtPlacedAt mpl ER 617 W)
        (mpl.ρ "memset") (mmpl.base 21))
    (hStub_mc : ∀ W : CliHooks,
      StubReachesTargetOn (F3CodeInv mpl mmpl) (cliProgExtPlacedAt mpl ER 617 W)
        (mpl.ρ "memcpy") (mmpl.base 20))
    (hRealHooks : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → F3CodeInv mpl mmpl u.mem → PredFs u.fs →
        ExecFrozen (f u).mem ∧ PredFs (f u).fs)
    (hSvcFs : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → F3CodeInv mpl mmpl z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs) :
    Block617TransferFixedHypG mpl mmpl EG ER (StdMainEntryLr f3StdLayout)
      (F3CodeOk mpl mmpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk :=
  (f3Block617TransferFixedG_memsetMemcpy_of_replaysOn_outcome PredFs hFs0 hghost_ms hghost_mc
    hother hreal_ms_none hreal_mc_none hreal_blk21_none hreal_blk20_none hblk21_ext hblk20_ext
    hStub_ms hStub_mc hRealHooks hSvcFs).mono_guard
    (fun _ hlr => f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr hMm hlr)

end

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard
