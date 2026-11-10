/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import ProofLib.SepLogic.WP.StepsProcess
import ProofLib.StdStartup.MemOps

/-!
# K-Route `W`-Independent `memcpy` Ghost Hook Instance (`ElfSlicesPqOomH2KMemcpy`)

Concrete `CliElfLib`-side K-convention `memcpy` ghost hook (Card `H-C9` Task 3 + `rev_c7.md` NITs
3b & 4c), mirroring `ElfSlicesPqOomH2KMemset` (`ba4d2cc002`) for `mallocngLib` block 20
(`memcpySymWords`, `396` B at `mmpl.base 20`):
1. `W`-independent `h2k_memcpyGhostHook[K]` via `f3LinkedCallHook hole2_keepSub hole2_emptyProg
   f3TrialRxProg (mmpl.base 20)`, plus `rfl` bridges `memcpySpecK_eq_h2k_withKeepLrFalse`.
2. Kernel-checked `f3TrialRxProg.hasWords (mmpl.base 20) memcpySymWords` (`rfl_kernel`).
3. Shared consumer `HookOk` / `HookFsTraced` / `VmPreserved` / `OomPreserved ∧ PoolPreserved` /
   `.oracle` suite (`hMm` only).
4. `W`-polymorphic replays, self & cross `Blk20TrapHook` / `Blk21TrapHook` coverage (`memcpy`,
   `memset`, `h2k_ghFixedK`), and `h2k_memcpyGhostHookNarrow` + `_stub_replayOn_of_trap_ret`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open ProofLib.StdStartup (checkWordsAt hasWords_of_wordTree)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memcpySymWords)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (
  framelessMemcpySpec memcpyROExtSpec sessionMemcpyRegionSpec sessionMemcpySpec withStack
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)
open CryptoVerification.SignalSession (
  CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsRustNoAllocShimSymCli
)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC cliGhostExterns)
open CryptoVerification.SignalSession.CliExt (memcpyROSpec memcpySpec)
open LibsignalBinary.Heap (OomPreserved PoolPreserved VmPreserved allocMemcpyVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (libcMemcpyCliSpec memcpyRegionCliSpec)
open LibsignalBinary.Heap.Fine (f3MallocngMpl f3RxWordCount)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  ActiveF3CallPre f3LinkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysS_of_single_stub
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  keepMemsetBlk21 withExecFrozen
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  activeF3CallPre_const_iff emptyStdProg f3EmptyMemsetGhostHook_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet (
  Blk21TrapHook blk21TrapHook_of_exception_on_keepLr
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  mallocngBlockProg20_externAt_none mallocngBlockProg20_hasWords
  masterMemcpySpec memcpySpecK
  subroutine_ok_masterMemcpy_of_hasWords subroutine_ok_masterMemcpyK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  keepCoversBlk20_keepMemcpyBlk20 keepMemcpyBlk20
  masterMemcpy_outcome_setPC masterMemcpy_pre_setPC
  masterMemcpyK_outcome_setPC masterMemcpyK_pre_setPC
  memcpyGhostHook memcpyGhostHookK
  memcpyGhostHook_allocMemcpyVm_ok memcpyGhostHook_any_execFrozen_ok
  memcpyGhostHook_any_memcpySpecK_ok
  memcpyGhostHook_cliMemcpy_budget_ok memcpyGhostHook_cliMemcpy_keepsFs_ok
  memcpyGhostHook_cliMemcpy_ok memcpyGhostHook_cliMemcpyRO_budget_ok
  memcpyGhostHook_cliMemcpyRO_keepsFs_ok memcpyGhostHook_cliMemcpyRO_ok
  memcpyGhostHook_framelessMemcpy_keepsFs_ok memcpyGhostHook_framelessMemcpy_ok
  memcpyGhostHook_framelessMemcpyAcp_ok memcpyGhostHook_framelessMemcpyBudget_keepsFs_ok
  memcpyGhostHook_framelessMemcpyBudget_ok memcpyGhostHook_framelessMemcpyBudgetFlat_ok
  memcpyGhostHook_libcMemcpy_budget_keepsFs_ok memcpyGhostHook_libcMemcpy_budget_ok
  memcpyGhostHook_libcMemcpy_keepsFs_ok memcpyGhostHook_libcMemcpy_ok
  memcpyGhostHook_libcMemcpyCli_ok
  memcpyGhostHook_master_ok
  memcpyGhostHook_memcpyROExt_budget_ok memcpyGhostHook_memcpyROExt_keepsFs_ok
  memcpyGhostHook_memcpyROExt_ok
  memcpyGhostHook_memcpyRegion_budget_ok memcpyGhostHook_memcpyRegion_budget_withStack_keepsFs_ok
  memcpyGhostHook_memcpyRegion_budget_withStack_ok memcpyGhostHook_memcpyRegion_keepsFs_ok
  memcpyGhostHook_memcpyRegion_ok memcpyGhostHook_memcpyRegion_withStack_keepsFs_ok
  memcpyGhostHook_memcpyRegion_withStack_ok memcpyGhostHook_memcpyRegionCli_ok
  memcpyGhostHook_oomPoolPreserved memcpyGhostHook_oracle
  memcpyGhostHook_sessionMemcpy_keepsFs_ok memcpyGhostHook_sessionMemcpy_ok
  memcpyGhostHook_sessionMemcpyBudget_keepsFs_ok memcpyGhostHook_sessionMemcpyBudget_ok
  memcpyGhostHook_sessionMemcpyRO4K_ok memcpyGhostHook_sessionMemcpyRO4KBudget_ok
  memcpyGhostHook_sessionMemcpyRegion_keepsFs_ok memcpyGhostHook_sessionMemcpyRegion_ok
  memcpyGhostHook_sessionMemcpyRegion_withStack_keepsFs_ok
  memcpyGhostHook_sessionMemcpyRegion_withStack_ok
  memcpyGhostHook_sessionMemcpyRegionBudget_ok
  memcpyGhostHook_sessionMemcpyRegionBudget_withStack_keepsFs_ok
  memcpyGhostHook_sessionMemcpyRegionBudget_withStack_ok
  memcpyGhostHook_sessionMemcpyRegionRO_budget_ok
  memcpyGhostHook_sessionMemcpyRegionRO_budget_withStack_keepsFs_ok
  memcpyGhostHook_sessionMemcpyRegionRO_budget_withStack_ok
  memcpyGhostHook_sessionMemcpyRegionRO_keepsFs_ok memcpyGhostHook_sessionMemcpyRegionRO_ok
  memcpyGhostHook_sessionMemcpyRegionRO_withStack_keepsFs_ok
  memcpyGhostHook_sessionMemcpyRegionRO_withStack_ok memcpyGhostHook_sessionMemcpyRegionROAcp_ok
  memcpyGhostHook_trace memcpyGhostHook_vmPreserved
  memcpyGhostHookK_masterK_ok memcpyGhostHookK_oomPoolPreserved
  memcpyGhostHookK_oracle memcpyGhostHookK_trace memcpyGhostHookK_vmPreserved
  specPreservesFsTrace_masterMemcpy specPreservesFsTrace_masterMemcpyK
  specStripSInvariant_masterMemcpy specStripSInvariant_masterMemcpyK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostK (
  memcpyGhostHookK_allocMemcpyVmK_ok memcpyGhostHookK_any_execFrozen_ok
  memcpyGhostHookK_cliMemcpyK_budget_ok memcpyGhostHookK_cliMemcpyK_keepsFs_ok
  memcpyGhostHookK_cliMemcpyK_ok memcpyGhostHookK_cliMemcpyROK_budget_ok
  memcpyGhostHookK_cliMemcpyROK_ok
  memcpyGhostHookK_framelessMemcpyAcpK_ok memcpyGhostHookK_framelessMemcpyBudgetFlatK_ok
  memcpyGhostHookK_framelessMemcpyBudgetK_keepsFs_ok memcpyGhostHookK_framelessMemcpyBudgetK_ok
  memcpyGhostHookK_framelessMemcpyK_keepsFs_ok memcpyGhostHookK_framelessMemcpyK_ok
  memcpyGhostHookK_libcMemcpyCliK_ok memcpyGhostHookK_libcMemcpyK_budget_keepsFs_ok
  memcpyGhostHookK_libcMemcpyK_budget_ok memcpyGhostHookK_libcMemcpyK_keepsFs_ok
  memcpyGhostHookK_libcMemcpyK_ok
  memcpyGhostHookK_memcpyROExtK_budget_ok memcpyGhostHookK_memcpyROExtK_ok
  memcpyGhostHookK_memcpyRegionCliK_ok memcpyGhostHookK_memcpyRegionK_budget_ok
  memcpyGhostHookK_memcpyRegionK_budget_withStack_keepsFs_ok
  memcpyGhostHookK_memcpyRegionK_budget_withStack_ok memcpyGhostHookK_memcpyRegionK_keepsFs_ok
  memcpyGhostHookK_memcpyRegionK_ok
  memcpyGhostHookK_sessionMemcpyBudgetK_keepsFs_ok memcpyGhostHookK_sessionMemcpyBudgetK_ok
  memcpyGhostHookK_sessionMemcpyK_keepsFs_ok memcpyGhostHookK_sessionMemcpyK_ok
  memcpyGhostHookK_sessionMemcpyRO4KBudgetK_ok memcpyGhostHookK_sessionMemcpyRO4KK_ok
  memcpyGhostHookK_sessionMemcpyRegionBudgetK_ok
  memcpyGhostHookK_sessionMemcpyRegionBudgetK_withStack_keepsFs_ok
  memcpyGhostHookK_sessionMemcpyRegionBudgetK_withStack_ok
  memcpyGhostHookK_sessionMemcpyRegionK_keepsFs_ok memcpyGhostHookK_sessionMemcpyRegionK_ok
  memcpyGhostHookK_sessionMemcpyRegionROAcpK_ok
  memcpyGhostHookK_sessionMemcpyRegionROK_budget_ok
  memcpyGhostHookK_sessionMemcpyRegionROK_budget_withStack_keepsFs_ok
  memcpyGhostHookK_sessionMemcpyRegionROK_budget_withStack_ok
  memcpyGhostHookK_sessionMemcpyRegionROK_keepsFs_ok memcpyGhostHookK_sessionMemcpyRegionROK_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn (
  codeLoaded_stripExecOutside_blk20
  f3EmptyMemcpyGhostHook f3EmptyMemcpyGhostHookK
  f3EmptyMemcpyGhostHook_eq f3EmptyMemcpyGhostHook_fs f3EmptyMemcpyGhostHook_fsT
  f3EmptyMemcpyGhostHookK_eq f3EmptyMemcpyGhostHookK_fs f3EmptyMemcpyGhostHookK_fsT
  f3EmptyMemcpyGhostHookK_keepLr_false_of_noException
  keepCoversBlk20_keepRange mallocngBlockProg20_svc_eq
)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact (
  HookExactMemcpy f3EmptyMemcpyGhostHook_exact f3EmptyMemcpyGhostHookK_exact_of_keepLr_false
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet (
  Blk20TrapHook blk20TrapHook_memcpyGhostHook blk20TrapHook_memsetGhostHook
  blk20TrapHook_of_exception_on_keepLr blk20_lr_trap_after_hook_ret
  blk21TrapHook_memcpyGhostHook
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced (
  f3CliElf_mallocng_linkedAt_unique
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (
  f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_stubs
  f3TrialRxProg_svc f3TrialRxProg_symbols f3TrialRxWordTree f3TrialRxWordTree_eq
  f3TrialRxWordTree_size
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_real_subroutine_run_visitedIn_of_stripS h2fsgen_stepsUntil_det
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (
  h2k_ghFixedK h2k_keepSubLr_false_of_noException h2k_withKeepLrFalse
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset (
  h2k_f3CodeInv_rxProg_keepSub h2k_keepSub_covers_blk21
  h2k_memsetGhostHook h2k_memsetGhostHookK
  h2k_memsetGhostHook_eq_f3Empty h2k_memsetGhostHookK_keepLr_false_of_noException
  hole2_keepSub_eq_keepRange_f3Rx
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2 (
  h2sl_steps_realW_of_visitedIn_keepSub
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst (
  hole2_emptyProg hole2_keepSub
)

/-! ## 1. K-Convention `W`-Independent Definitions & Definitional (`rfl`) Bridges (`rev_c7.md` NIT 3b) -/

/-- `MemcpyCode.memcpySpecK` is definitionally identical (`rfl`) to
    `ElfSlicesPqOomH2KHooks.h2k_withKeepLrFalse`. -/
theorem memcpySpecK_eq_h2k_withKeepLrFalse {α : Type} (keep : BitVec 64 → Bool) (spec : Spec α) :
    memcpySpecK keep spec = h2k_withKeepLrFalse keep spec := rfl

/-- Concrete `hole2_keepSub` + `masterMemcpySpec` definitional pin (`rev_c7.md` NIT 3b). -/
theorem memcpySpecK_hole2_master_eq_h2k_withKeepLrFalse :
    memcpySpecK hole2_keepSub masterMemcpySpec =
      h2k_withKeepLrFalse hole2_keepSub masterMemcpySpec := rfl

/-- Plain `W`-independent K-convention `memcpy` ghost hook (`h2k_memcpyGhostHook`). -/
@[expose] noncomputable def h2k_memcpyGhostHook (mmpl : MultiPlacement) : State → State :=
  f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg (mmpl.base 20)
    (fun _ _ => masterMemcpySpec) hookMemcpy

/-- `K`-narrowed `W`-independent K-convention `memcpy` ghost hook (`h2k_memcpyGhostHookK`),
    matching `h2k_ghFixedK` (`ElfSlicesPqOomH2KHooks.lean:559`) and `h2k_memsetGhostHookK`. -/
@[expose] noncomputable def h2k_memcpyGhostHookK (mmpl : MultiPlacement) : State → State :=
  f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg (mmpl.base 20)
    (fun _ _ => h2k_withKeepLrFalse hole2_keepSub masterMemcpySpec) hookMemcpy

theorem h2k_memcpyGhostHook_eq_f3Empty (mmpl : MultiPlacement) :
    h2k_memcpyGhostHook mmpl =
      f3EmptyMemcpyGhostHook hole2_keepSub f3TrialRxProg (mmpl.base 20) := rfl

theorem h2k_memcpyGhostHookK_eq_f3EmptyK (mmpl : MultiPlacement) :
    h2k_memcpyGhostHookK mmpl =
      f3EmptyMemcpyGhostHookK hole2_keepSub f3TrialRxProg (mmpl.base 20) := rfl

theorem h2k_memcpyGhostHook_eq (mmpl : MultiPlacement) :
    h2k_memcpyGhostHook mmpl =
      memcpyGhostHook hole2_keepSub emptyStdProg f3TrialRxProg (mmpl.base 20) :=
  f3EmptyMemcpyGhostHook_eq hole2_keepSub f3TrialRxProg (mmpl.base 20)

theorem h2k_memcpyGhostHookK_eq (mmpl : MultiPlacement) :
    h2k_memcpyGhostHookK mmpl =
      memcpyGhostHookK hole2_keepSub emptyStdProg f3TrialRxProg (mmpl.base 20) :=
  f3EmptyMemcpyGhostHookK_eq hole2_keepSub f3TrialRxProg (mmpl.base 20)

/-! ## 2. Kernel-Checked `f3TrialRxProg.hasWords (mmpl.base 20) memcpySymWords` -/

private theorem memcpySymWords_len_le : memcpySymWords.length ≤ 1024 :=
  Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memcpySymWords.length 1024 = true)

set_option maxRecDepth 4000000 in
private theorem h2k_f3Trial_blk20_chk :
    checkWordsAt f3TrialRxWordTree
      (f3MallocngMpl.base 20 - f3RxSegBase).toNat memcpySymWords = true := by
  rfl_kernel

/-- Unconditional kernel-checked `hasWords` for `memcpySymWords` at `f3MallocngMpl.base 20` inside
    `f3TrialRxProg`. -/
theorem h2k_f3TrialRxProg_hasWords_blk20_f3 :
    f3TrialRxProg.hasWords (f3MallocngMpl.base 20) memcpySymWords := by
  have hoff_lt : (f3MallocngMpl.base 20 - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen := memcpySymWords_len_le
  exact hasWords_of_wordTree f3RxWordCount
    f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by omega)
    f3TrialRxProg_stubs f3TrialRxProg_symbols h2k_f3Trial_blk20_chk

/-- `f3TrialRxProg` holds `memcpySymWords` at `mmpl.base 20` for every `mmpl` satisfying
    `mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem h2k_f3TrialRxProg_hasWords_blk20 {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    f3TrialRxProg.hasWords (mmpl.base 20) memcpySymWords := by
  have h20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  have hbase : mmpl.base 20 = f3MallocngMpl.base 20 :=
    (f3CliElf_mallocng_linkedAt_unique hMm).1 20 h20
  rw [hbase]
  exact h2k_f3TrialRxProg_hasWords_blk20_f3

/-! ## 3. State / Frame / Shared Consumer `HookOk` Suite (`hMm` Only, `W`-Independent) -/

theorem h2k_memcpyGhostHook_fs (mmpl : MultiPlacement) (s0 : State) :
    (h2k_memcpyGhostHook mmpl s0).fs = s0.fs :=
  f3EmptyMemcpyGhostHook_fs hole2_keepSub f3TrialRxProg (mmpl.base 20) s0

theorem h2k_memcpyGhostHookK_fs (mmpl : MultiPlacement) (s0 : State) :
    (h2k_memcpyGhostHookK mmpl s0).fs = s0.fs :=
  f3EmptyMemcpyGhostHookK_fs hole2_keepSub f3TrialRxProg (mmpl.base 20) s0

theorem h2k_memcpyGhostHook_fsT (mmpl : MultiPlacement) :
    HookFsTraced IsFsC (h2k_memcpyGhostHook mmpl) :=
  f3EmptyMemcpyGhostHook_fsT hole2_keepSub f3TrialRxProg (mmpl.base 20)

theorem h2k_memcpyGhostHookK_fsT (mmpl : MultiPlacement) :
    HookFsTraced IsFsC (h2k_memcpyGhostHookK mmpl) :=
  f3EmptyMemcpyGhostHookK_fsT hole2_keepSub f3TrialRxProg (mmpl.base 20)

theorem h2k_memcpyGhostHookK_keepLr_false_of_noException
    {mmpl : MultiPlacement} {u : State}
    (hnoex : ∀ msg, (h2k_memcpyGhostHookK mmpl u).status ≠ .Exception msg) :
    hole2_keepSub (u.readReg64 .lr) = false :=
  f3EmptyMemcpyGhostHookK_keepLr_false_of_noException hnoex

section ConsumerContracts

variable {mmpl : MultiPlacement} (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
include hMm

theorem h2k_memcpyGhostHook_trace (s0 : State) :
    (h2k_memcpyGhostHook mmpl s0).trace = s0.trace := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_trace rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) s0
theorem h2k_memcpyGhostHookK_trace (s0 : State) :
    (h2k_memcpyGhostHookK mmpl s0).trace = s0.trace := by
  rw [h2k_memcpyGhostHookK_eq]; exact memcpyGhostHookK_trace rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) s0
theorem h2k_memcpyGhostHook_vmPreserved (s0 : State) :
    VmPreserved s0 (h2k_memcpyGhostHook mmpl s0) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_vmPreserved rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) s0
theorem h2k_memcpyGhostHookK_vmPreserved (s0 : State) :
    VmPreserved s0 (h2k_memcpyGhostHookK mmpl s0) := by
  rw [h2k_memcpyGhostHookK_eq]; exact memcpyGhostHookK_vmPreserved rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) s0
theorem h2k_memcpyGhostHook_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (h2k_memcpyGhostHook mmpl s0) ∧
    PoolPreserved s0 (h2k_memcpyGhostHook mmpl s0) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_oomPoolPreserved rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) s0
theorem h2k_memcpyGhostHookK_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (h2k_memcpyGhostHookK mmpl s0) ∧
    PoolPreserved s0 (h2k_memcpyGhostHookK mmpl s0) := by
  rw [h2k_memcpyGhostHookK_eq]; exact memcpyGhostHookK_oomPoolPreserved rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) s0
theorem h2k_memcpyGhostHook_oracle (s0 : State) :
    (h2k_memcpyGhostHook mmpl s0).oracle = s0.oracle := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_oracle rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) s0
theorem h2k_memcpyGhostHookK_oracle (s0 : State) :
    (h2k_memcpyGhostHookK mmpl s0).oracle = s0.oracle := by
  rw [h2k_memcpyGhostHookK_eq]; exact memcpyGhostHookK_oracle rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) s0

theorem h2k_memcpyGhostHook_master_ok :
    HookOk (h2k_memcpyGhostHook mmpl) masterMemcpySpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_master_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_masterK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub masterMemcpySpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_masterK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext
    (h2k_f3TrialRxProg_hasWords_blk20 hMm)

theorem h2k_memcpyGhostHook_libcMemcpy_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (libcMemcpySpec stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_libcMemcpy_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_sessionMemcpy_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (sessionMemcpySpec stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpy_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_cliMemcpy_ok :
    HookOk (h2k_memcpyGhostHook mmpl) memcpySpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_cliMemcpy_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_memcpyRegion_ok :
    HookOk (h2k_memcpyGhostHook mmpl) memcpyRegionSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyRegion_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRegion_ok :
    HookOk (h2k_memcpyGhostHook mmpl) sessionMemcpyRegionSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegion_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_framelessMemcpy_ok :
    HookOk (h2k_memcpyGhostHook mmpl) framelessMemcpySpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_framelessMemcpy_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRegionRO_ok :
    HookOk (h2k_memcpyGhostHook mmpl) CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegionRO_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_memcpyROExt_ok (stk : Nat := 16384) :
    HookOk (h2k_memcpyGhostHook mmpl) (memcpyROExtSpec stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyROExt_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_cliMemcpyRO_ok :
    HookOk (h2k_memcpyGhostHook mmpl) memcpyROSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_cliMemcpyRO_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRO4K_ok :
    HookOk (h2k_memcpyGhostHook mmpl) CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRO4K_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_libcMemcpy_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (libcMemcpySpec stk).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_libcMemcpy_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_sessionMemcpy_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (sessionMemcpySpec stk).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpy_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_cliMemcpy_keepsFs_ok :
    HookOk (h2k_memcpyGhostHook mmpl) memcpySpec.keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_cliMemcpy_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_memcpyRegion_keepsFs_ok :
    HookOk (h2k_memcpyGhostHook mmpl) memcpyRegionSpec.keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyRegion_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_memcpyRegion_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (withStack memcpyRegionSpec stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyRegion_withStack_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_memcpyRegion_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (withStack memcpyRegionSpec stk).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyRegion_withStack_keepsFs_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_sessionMemcpyRegion_keepsFs_ok :
    HookOk (h2k_memcpyGhostHook mmpl) sessionMemcpyRegionSpec.keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegion_keepsFs_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRegion_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (withStack sessionMemcpyRegionSpec stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegion_withStack_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_sessionMemcpyRegion_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (withStack sessionMemcpyRegionSpec stk).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegion_withStack_keepsFs_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_framelessMemcpy_keepsFs_ok :
    HookOk (h2k_memcpyGhostHook mmpl) framelessMemcpySpec.keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_framelessMemcpy_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRegionRO_keepsFs_ok :
    HookOk (h2k_memcpyGhostHook mmpl)
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec.keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegionRO_keepsFs_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRegionRO_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl)
      (withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegionRO_withStack_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_sessionMemcpyRegionRO_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl)
      (withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegionRO_withStack_keepsFs_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_memcpyROExt_keepsFs_ok (stk : Nat := 16384) :
    HookOk (h2k_memcpyGhostHook mmpl) (memcpyROExtSpec stk).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyROExt_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_cliMemcpyRO_keepsFs_ok :
    HookOk (h2k_memcpyGhostHook mmpl) memcpyROSpec.keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_cliMemcpyRO_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_libcMemcpy_budget_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (withVmPreserved (libcMemcpySpec stk)) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_libcMemcpy_budget_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_libcMemcpy_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (withVmPreserved (libcMemcpySpec stk)).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_libcMemcpy_budget_keepsFs_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_sessionMemcpyBudget_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (sessionMemcpyBudgetSpec stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyBudget_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_sessionMemcpyBudget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (sessionMemcpyBudgetSpec stk).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyBudget_keepsFs_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_cliMemcpy_budget_ok :
    HookOk (h2k_memcpyGhostHook mmpl) (withVmPreserved memcpySpec) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_cliMemcpy_budget_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_memcpyRegion_budget_ok :
    HookOk (h2k_memcpyGhostHook mmpl) (withVmPreserved memcpyRegionSpec) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyRegion_budget_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_memcpyRegion_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (withStack (withVmPreserved memcpyRegionSpec) stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyRegion_budget_withStack_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_memcpyRegion_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (withStack (withVmPreserved memcpyRegionSpec) stk).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyRegion_budget_withStack_keepsFs_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_sessionMemcpyRegionBudget_ok :
    HookOk (h2k_memcpyGhostHook mmpl) sessionMemcpyRegionBudgetSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegionBudget_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRegionBudget_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (withStack sessionMemcpyRegionBudgetSpec stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegionBudget_withStack_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_sessionMemcpyRegionBudget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (withStack sessionMemcpyRegionBudgetSpec stk).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegionBudget_withStack_keepsFs_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_framelessMemcpyBudget_ok :
    HookOk (h2k_memcpyGhostHook mmpl) framelessMemcpyBudgetSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_framelessMemcpyBudget_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_framelessMemcpyBudget_keepsFs_ok :
    HookOk (h2k_memcpyGhostHook mmpl) framelessMemcpyBudgetSpec.keepsFs := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_framelessMemcpyBudget_keepsFs_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_framelessMemcpyBudgetFlat_ok :
    HookOk (h2k_memcpyGhostHook mmpl)
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_framelessMemcpyBudgetFlat_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRegionRO_budget_ok :
    HookOk (h2k_memcpyGhostHook mmpl)
      (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegionRO_budget_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRegionRO_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl)
      (withStack (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegionRO_budget_withStack_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_sessionMemcpyRegionRO_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl)
      (withStack
        (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) stk).keepsFs := by
  rw [h2k_memcpyGhostHook_eq]
  exact memcpyGhostHook_sessionMemcpyRegionRO_budget_withStack_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_memcpyROExt_budget_ok (stk : Nat := 16384) :
    HookOk (h2k_memcpyGhostHook mmpl) (withVmPreserved (memcpyROExtSpec stk)) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyROExt_budget_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHook_cliMemcpyRO_budget_ok :
    HookOk (h2k_memcpyGhostHook mmpl) (withVmPreserved memcpyROSpec) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_cliMemcpyRO_budget_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRO4KBudget_ok :
    HookOk (h2k_memcpyGhostHook mmpl)
      LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget.sessionMemcpyROSpec4K := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRO4KBudget_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_framelessMemcpyAcp_ok :
    HookOk (h2k_memcpyGhostHook mmpl)
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_framelessMemcpyAcp_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_sessionMemcpyRegionROAcp_ok :
    HookOk (h2k_memcpyGhostHook mmpl)
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_sessionMemcpyRegionROAcp_ok rfl
    f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_allocMemcpyVm_ok :
    HookOk (h2k_memcpyGhostHook mmpl) allocMemcpyVmSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_allocMemcpyVm_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_memcpyRegionCli_ok :
    HookOk (h2k_memcpyGhostHook mmpl) memcpyRegionCliSpec := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_memcpyRegionCli_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHook_libcMemcpyCli_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHook mmpl) (libcMemcpyCliSpec stk) := by
  rw [h2k_memcpyGhostHook_eq]; exact memcpyGhostHook_libcMemcpyCli_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk

omit hMm in
theorem h2k_memcpyGhostHook_any_execFrozen_ok {α : Type} {spec : Spec α}
    (hok : HookOk (h2k_memcpyGhostHook mmpl) spec) :
    HookOk (h2k_memcpyGhostHook mmpl) (withExecFrozen spec) := by
  rw [h2k_memcpyGhostHook_eq] at hok ⊢
  exact memcpyGhostHook_any_execFrozen_ok hok

omit hMm in
theorem h2k_memcpyGhostHook_any_withKeepLrFalse_ok {α : Type} {spec : Spec α}
    (hok : HookOk (h2k_memcpyGhostHook mmpl) spec) :
    HookOk (h2k_memcpyGhostHook mmpl) (h2k_withKeepLrFalse hole2_keepSub spec) := by
  rw [h2k_memcpyGhostHook_eq] at hok ⊢
  rw [← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHook_any_memcpySpecK_ok hok

-- `h2k_withKeepLrFalse hole2_keepSub`-narrowed consumer contracts on `h2k_memcpyGhostHookK`:

theorem h2k_memcpyGhostHookK_libcMemcpyK_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (libcMemcpySpec stk)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_libcMemcpyK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_sessionMemcpyK_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (sessionMemcpySpec stk)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_cliMemcpyK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub memcpySpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_cliMemcpyK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_memcpyRegionK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub memcpyRegionSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_memcpyRegionK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub sessionMemcpyRegionSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_framelessMemcpyK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub framelessMemcpySpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_framelessMemcpyK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionROK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionROK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_memcpyROExtK_ok (stk : Nat := 16384) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (memcpyROExtSpec stk)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_memcpyROExtK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_cliMemcpyROK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub memcpyROSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_cliMemcpyROK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_sessionMemcpyRO4KK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRO4KK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_libcMemcpyK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (libcMemcpySpec stk).keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_libcMemcpyK_keepsFs_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_sessionMemcpyK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (sessionMemcpySpec stk).keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyK_keepsFs_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_cliMemcpyK_keepsFs_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub memcpySpec.keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_cliMemcpyK_keepsFs_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_memcpyRegionK_keepsFs_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub memcpyRegionSpec.keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_memcpyRegionK_keepsFs_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionK_keepsFs_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub sessionMemcpyRegionSpec.keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionK_keepsFs_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_framelessMemcpyK_keepsFs_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub framelessMemcpySpec.keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_framelessMemcpyK_keepsFs_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionROK_keepsFs_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec.keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionROK_keepsFs_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_libcMemcpyK_budget_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved (libcMemcpySpec stk))) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_libcMemcpyK_budget_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_libcMemcpyK_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved (libcMemcpySpec stk)).keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_libcMemcpyK_budget_keepsFs_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_sessionMemcpyBudgetK_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (sessionMemcpyBudgetSpec stk)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyBudgetK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_sessionMemcpyBudgetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (sessionMemcpyBudgetSpec stk).keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyBudgetK_keepsFs_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_cliMemcpyK_budget_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved memcpySpec)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_cliMemcpyK_budget_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_memcpyRegionK_budget_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved memcpyRegionSpec)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_memcpyRegionK_budget_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_memcpyRegionK_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (withStack (withVmPreserved memcpyRegionSpec) stk)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_memcpyRegionK_budget_withStack_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_memcpyRegionK_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        (withStack (withVmPreserved memcpyRegionSpec) stk).keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_memcpyRegionK_budget_withStack_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionBudgetK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub sessionMemcpyRegionBudgetSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionBudgetK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionBudgetK_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (withStack sessionMemcpyRegionBudgetSpec stk)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionBudgetK_withStack_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionBudgetK_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        (withStack sessionMemcpyRegionBudgetSpec stk).keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionBudgetK_withStack_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_framelessMemcpyBudgetK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub framelessMemcpyBudgetSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_framelessMemcpyBudgetK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_framelessMemcpyBudgetK_keepsFs_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub framelessMemcpyBudgetSpec.keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_framelessMemcpyBudgetK_keepsFs_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_framelessMemcpyBudgetFlatK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_framelessMemcpyBudgetFlatK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionROK_budget_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionROK_budget_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionROK_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        (withStack (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) stk)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionROK_budget_withStack_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionROK_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        (withStack
          (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) stk).keepsFs) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionROK_budget_withStack_keepsFs_ok rfl f3TrialRxProg_svc
    (fun _ _ => rfl) f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_memcpyROExtK_budget_ok (stk : Nat := 16384) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved (memcpyROExtSpec stk))) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_memcpyROExtK_budget_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk
theorem h2k_memcpyGhostHookK_cliMemcpyROK_budget_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved memcpyROSpec)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_cliMemcpyROK_budget_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_sessionMemcpyRO4KBudgetK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget.sessionMemcpyROSpec4K) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRO4KBudgetK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_framelessMemcpyAcpK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_framelessMemcpyAcpK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_sessionMemcpyRegionROAcpK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub
        LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_sessionMemcpyRegionROAcpK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_allocMemcpyVmK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub allocMemcpyVmSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_allocMemcpyVmK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_memcpyRegionCliK_ok :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub memcpyRegionCliSpec) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_memcpyRegionCliK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm)
theorem h2k_memcpyGhostHookK_libcMemcpyCliK_ok (stk : Nat := 4096) :
    HookOk (h2k_memcpyGhostHookK mmpl)
      (h2k_withKeepLrFalse hole2_keepSub (libcMemcpyCliSpec stk)) := by
  rw [h2k_memcpyGhostHookK_eq, ← memcpySpecK_eq_h2k_withKeepLrFalse]
  exact memcpyGhostHookK_libcMemcpyCliK_ok rfl f3TrialRxProg_svc (fun _ _ => rfl)
    f3TrialRxProg_no_ext (h2k_f3TrialRxProg_hasWords_blk20 hMm) stk

omit hMm in
theorem h2k_memcpyGhostHookK_any_execFrozen_ok {α : Type} {spec : Spec α}
    (hok : HookOk (h2k_memcpyGhostHookK mmpl) spec) :
    HookOk (h2k_memcpyGhostHookK mmpl) (withExecFrozen spec) := by
  rw [h2k_memcpyGhostHookK_eq] at hok ⊢
  exact memcpyGhostHookK_any_execFrozen_ok hok

end ConsumerContracts

/-! ## 4. `W`-Polymorphic Replays via `h2sl_steps_realW_of_visitedIn_keepSub` -/

private theorem stepsVisitedIn_mono {D1 D2 : BitVec 64 → Bool} {P1 : Program} {s sf : State}
    (h : ∀ pc, D1 pc = true → D2 pc = true) (hvis : h2fsgen_StepsVisitedIn D1 P1 s sf) :
    h2fsgen_StepsVisitedIn D2 P1 s sf := by
  induction hvis with
  | refl u => exact .refl u
  | step hd h1 _ ih => exact .step (h _ hd) h1 ih

private theorem f3LinkedCallHook_empty_visitedIn {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entryTarget spec) (hInvS : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => spec) fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => spec) fallback u
    h2fsgen_StepsVisitedIn keep hole2_emptyProg (u.setPC entryTarget) sf_g ∧
      ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  classical
  have hActPre : ActiveF3CallPre (fun _ _ => spec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3LinkedCallHook; simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ := (activeF3CallPre_const_iff spec u).mp hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS (P1 := emptyStdProg) rfl hsvc_sub
      (fun _ _ => rfl) hsub_no hOk hInvS hFsT hPrePC hOutPC hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => spec) fallback u =
      sf := by
    unfold f3LinkedCallHook; simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  dsimp only; rw [heq]; exact ⟨hvis, hfr_sf, hfs⟩

/-- Target-entry `W`-polymorphic replay for `h2k_memcpyGhostHook`. -/
theorem h2k_memcpyGhostHook_target_replay
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (h2k_memcpyGhostHook mmpl u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (mmpl.base 20)) (h2k_memcpyGhostHook mmpl u) ∧
      ExecFrozen (h2k_memcpyGhostHook mmpl u).mem ∧
      F3CodeInv mpl mmpl (h2k_memcpyGhostHook mmpl u).mem ∧
      (h2k_memcpyGhostHook mmpl u).fs = u.fs := by
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
    f3LinkedCallHook_empty_visitedIn f3TrialRxProg_svc f3TrialRxProg_no_ext
      (subroutine_ok_masterMemcpy_of_hasWords f3TrialRxProg_no_ext
        (h2k_f3TrialRxProg_hasWords_blk20 hMm))
      (specStripSInvariant_masterMemcpy hole2_keepSub) specPreservesFsTrace_masterMemcpy
      masterMemcpy_pre_setPC masterMemcpy_outcome_setPC hrun hnoex hFr hlr_out
      (h2k_f3CodeInv_rxProg_keepSub hInv)
  have hSteps := h2sl_steps_realW_of_visitedIn_keepSub hLs mmpl W hvis
  exact ⟨hSteps, hfr_sf, hInv.of_keepsFrozen hSteps.keepsFrozen, hfs_sf⟩

/-- Target-entry `W`-polymorphic replay for `h2k_memcpyGhostHookK` (zero caller `lr` hypothesis). -/
theorem h2k_memcpyGhostHookK_target_replay
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (h2k_memcpyGhostHookK mmpl u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (mmpl.base 20)) (h2k_memcpyGhostHookK mmpl u) ∧
      ExecFrozen (h2k_memcpyGhostHookK mmpl u).mem ∧
      F3CodeInv mpl mmpl (h2k_memcpyGhostHookK mmpl u).mem ∧
      (h2k_memcpyGhostHookK mmpl u).fs = u.fs := by
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
    f3LinkedCallHook_empty_visitedIn f3TrialRxProg_svc f3TrialRxProg_no_ext
      (subroutine_ok_masterMemcpyK_of_hasWords hole2_keepSub f3TrialRxProg_no_ext
        (h2k_f3TrialRxProg_hasWords_blk20 hMm))
      (specStripSInvariant_masterMemcpyK hole2_keepSub)
      (specPreservesFsTrace_masterMemcpyK hole2_keepSub)
      (masterMemcpyK_pre_setPC hole2_keepSub) (masterMemcpyK_outcome_setPC hole2_keepSub)
      hrun hnoex hFr (f3EmptyMemcpyGhostHookK_keepLr_false_of_noException hnoex)
      (h2k_f3CodeInv_rxProg_keepSub hInv)
  have hSteps := h2sl_steps_realW_of_visitedIn_keepSub hLs mmpl W hvis
  exact ⟨hSteps, hfr_sf, hInv.of_keepsFrozen hSteps.keepsFrozen, hfs_sf⟩

/-- Behind-stub `W`-polymorphic guarded `On` replay for `h2k_memcpyGhostHook`. -/
theorem h2k_memcpyGhostHook_stub_replayOn
    {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc =
      none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 20)) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (h2k_memcpyGhostHook mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
          (h2k_memcpyGhostHook mmpl u) ∧
        ExecFrozen (h2k_memcpyGhostHook mmpl u).mem ∧
        F3CodeInv mpl mmpl (h2k_memcpyGhostHook mmpl u).mem ∧
        (h2k_memcpyGhostHook mmpl u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hInv => ?_⟩
  obtain ⟨hBody, hfr_sf, hInv_sf, hfs_sf⟩ :=
    h2k_memcpyGhostHook_target_replay hLs hMm W hrun hnoex hfr hlr hInv
  exact ⟨(hStub u hpc hrun hfr hInv).trans hBody, hfr_sf, hInv_sf, hfs_sf⟩

/-- Behind-stub `W`-polymorphic guarded `On` replay for `h2k_memcpyGhostHookK` (zero caller `lr`
    hypothesis). -/
theorem h2k_memcpyGhostHookK_stub_replayOn
    {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc =
      none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 20)) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (h2k_memcpyGhostHookK mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
          (h2k_memcpyGhostHookK mmpl u) ∧
        ExecFrozen (h2k_memcpyGhostHookK mmpl u).mem ∧
        F3CodeInv mpl mmpl (h2k_memcpyGhostHookK mmpl u).mem ∧
        (h2k_memcpyGhostHookK mmpl u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hInv => ?_⟩
  obtain ⟨hBody, hfr_sf, hInv_sf, hfs_sf⟩ :=
    h2k_memcpyGhostHookK_target_replay hLs hMm W hrun hnoex hfr hInv
  exact ⟨(hStub u hpc hrun hfr hInv).trans hBody, hfr_sf, hInv_sf, hfs_sf⟩

/-- Single-row `GhostExternReplaysS` for `h2k_memcpyGhostHook`. -/
theorem h2k_memcpyGhostHook_replaysS
    {P_ghost : Program} {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks)
    (hghost_stub : P_ghost.externAt? stubPc = some (h2k_memcpyGhostHook mmpl))
    (hother : ∀ pc, pc ≠ stubPc →
      P_ghost.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    (hreal_fr : ∀ pc f,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc =
      none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 20)) :
    GhostExternReplaysS hole2_keepSub (fun u => F3CodeInv mpl mmpl u.mem) P_ghost
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) := by
  have hRep := h2k_memcpyGhostHook_stub_replayOn hLs hMm W hreal_stub_none hStub
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hInv => ⟨hreal_fr pc f hr u hrun hfr, hInv.of_keepsFrozen hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hInv =>
      let ⟨hs, hfr', hInv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hInv
      ⟨hs, hfr', hInv'⟩⟩

/-- Single-row `GhostExternReplaysS` for `h2k_memcpyGhostHookK` (polymorphic in `keep_any`). -/
theorem h2k_memcpyGhostHookK_replaysS
    (keep_any : BitVec 64 → Bool)
    {P_ghost : Program} {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks)
    (hghost_stub : P_ghost.externAt? stubPc = some (h2k_memcpyGhostHookK mmpl))
    (hother : ∀ pc, pc ≠ stubPc →
      P_ghost.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    (hreal_fr : ∀ pc f,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc =
      none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 20)) :
    GhostExternReplaysS keep_any (fun u => F3CodeInv mpl mmpl u.mem) P_ghost
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) := by
  have hRep := h2k_memcpyGhostHookK_stub_replayOn hLs hMm W hreal_stub_none hStub
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hInv => ⟨hreal_fr pc f hr u hrun hfr, hInv.of_keepsFrozen hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hInv =>
      let ⟨hs, hfr', hInv', _⟩ := hRep.2 u hpc hrun hnoex hfr hInv
      ⟨hs, hfr', hInv'⟩⟩

/-! ## 5. `(A2)` `Blk20TrapHook` & Cross `Blk21TrapHook` Coverage (`rev_c7.md` NIT 4c) -/

/-- `hole2_keepSub` covers `keepMemcpyBlk20 mmpl` (`396` B at `mmpl.base 20`) for every `mmpl`
    satisfying `mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem h2k_keepSub_covers_blk20 {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, keepMemcpyBlk20 mmpl a = true → hole2_keepSub a = true := by
  have h20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  have hbase : mmpl.base 20 = f3MallocngMpl.base 20 :=
    (f3CliElf_mallocng_linkedAt_unique hMm).1 20 h20
  have hcov_f3 : ∀ off : Nat, off < 396 →
      hole2_keepSub (f3MallocngMpl.base 20 + BitVec.ofNat 64 off) = true := by
    rw [hole2_keepSub_eq_keepRange_f3Rx]
    exact keepCoversBlk20_keepRange f3RxSegBase.toNat (f3RxSegBase.toNat + 4 * f3RxWordCount)
      (by decide) (by decide) (by decide)
  intro a hka
  have hoff_lt : (a - mmpl.base 20).toNat < 396 := of_decide_eq_true hka
  have ha_eq : a = f3MallocngMpl.base 20 + BitVec.ofNat 64 (a - mmpl.base 20).toNat := by
    rw [← hbase, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm (mmpl.base 20),
      BitVec.sub_add_cancel]
  rw [ha_eq]
  exact hcov_f3 _ hoff_lt

private theorem exception_of_keepLr_false_of_noException
    {keep : BitVec 64 → Bool} {f : State → State} {w : State}
    (hnoex_imp : (∀ msg, (f w).status ≠ .Exception msg) → keep (w.readReg64 .lr) = false)
    (hkw : keep (w.readReg64 .lr) = true) :
    ∃ msg, (f w).status = .Exception msg := by
  classical
  by_contra hnone
  have hfalse : keep (w.readReg64 .lr) = false :=
    hnoex_imp fun msg hst => hnone ⟨msg, hst⟩
  rw [hkw] at hfalse
  exact Bool.noConfusion hfalse

/-- Plain `h2k_memcpyGhostHook mmpl` satisfies `Blk20TrapHook L` for every `L ∈ blk20`. -/
theorem h2k_memcpyGhostHook_blk20TrapHook {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L (h2k_memcpyGhostHook mmpl) := by
  intro L hL
  rw [h2k_memcpyGhostHook_eq]
  exact blk20TrapHook_memcpyGhostHook emptyStdProg f3TrialRxProg (mmpl.base 20)
    (h2k_keepSub_covers_blk20 hMm L hL)

/-- `K`-narrowed `h2k_memcpyGhostHookK mmpl` satisfies `Blk20TrapHook L` for every `L ∈ blk20`. -/
theorem h2k_memcpyGhostHookK_blk20TrapHook {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L (h2k_memcpyGhostHookK mmpl) :=
  fun L hL =>
    blk20TrapHook_of_exception_on_keepLr (h2k_keepSub_covers_blk20 hMm L hL) fun _ hkw =>
      exception_of_keepLr_false_of_noException h2k_memcpyGhostHookK_keepLr_false_of_noException hkw

/-- **Cross trap-hook (`memcpy` → `blk21`):** plain `h2k_memcpyGhostHook mmpl` satisfies
    `Blk21TrapHook L` for every `L ∈ blk21`. -/
theorem h2k_memcpyGhostHook_blk21TrapHook {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L (h2k_memcpyGhostHook mmpl) := by
  intro L hL
  rw [h2k_memcpyGhostHook_eq]
  exact blk21TrapHook_memcpyGhostHook emptyStdProg f3TrialRxProg (mmpl.base 20)
    (h2k_keepSub_covers_blk21 hMm L hL)

/-- **Cross trap-hook (`memcpyK` → `blk21`):** `K`-narrowed `h2k_memcpyGhostHookK mmpl` satisfies
    `Blk21TrapHook L` for every `L ∈ blk21`. -/
theorem h2k_memcpyGhostHookK_blk21TrapHook {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L (h2k_memcpyGhostHookK mmpl) :=
  fun L hL =>
    blk21TrapHook_of_exception_on_keepLr (h2k_keepSub_covers_blk21 hMm L hL) fun _ hkw =>
      exception_of_keepLr_false_of_noException h2k_memcpyGhostHookK_keepLr_false_of_noException hkw

/-- **Cross trap-hook (`memset` → `blk20`):** plain `h2k_memsetGhostHook mmpl` satisfies
    `Blk20TrapHook L` for every `L ∈ blk20`. -/
theorem h2k_memsetGhostHook_blk20TrapHook {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L (h2k_memsetGhostHook mmpl) := by
  intro L hL
  rw [h2k_memsetGhostHook_eq_f3Empty, f3EmptyMemsetGhostHook_eq]
  exact blk20TrapHook_memsetGhostHook emptyStdProg f3TrialRxProg (mmpl.base 21)
    (h2k_keepSub_covers_blk20 hMm L hL)

/-- **Cross trap-hook (`memsetK` → `blk20`):** `K`-narrowed `h2k_memsetGhostHookK mmpl` satisfies
    `Blk20TrapHook L` for every `L ∈ blk20`. -/
theorem h2k_memsetGhostHookK_blk20TrapHook {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L (h2k_memsetGhostHookK mmpl) :=
  fun L hL =>
    blk20TrapHook_of_exception_on_keepLr (h2k_keepSub_covers_blk20 hMm L hL) fun _ hkw =>
      exception_of_keepLr_false_of_noException h2k_memsetGhostHookK_keepLr_false_of_noException hkw

private theorem keep_true_of_fetchMem_stripExecOutside
    {P : Program} {keep : BitVec 64 → Bool} {m wmem : Memory} {pc : BitVec 64} {inst : Instr}
    (hperm : m.perm = (ProofLib.stripExecOutside keep wmem).perm)
    (hfm : P.fetchMem m pc = some inst) :
    keep pc = true := by
  unfold Program.fetchMem at hfm
  split at hfm
  · cases hfm
  · split at hfm
    · cases hfm
    · split at hfm
      · cases hfm
      · rename_i hcan
        have hcan' : m.canExec pc 4 = true := by
          cases hc : m.canExec pc 4
          · simp [hc] at hcan
          · rfl
        unfold Memory.canExec Memory.allPerm at hcan'
        simp only [Bool.and_eq_true] at hcan'
        have hx : (m.perm pc).x = true := hcan'.1
        have hp : m.perm pc = (ProofLib.stripExecOutside keep wmem).perm pc :=
          congrFun hperm pc
        rw [hp] at hx
        exact (ProofLib.strip_perm_x_imp hx).2

private def isBlk21LrPreserving (inst : Instr) : Bool :=
  match inst with
  | .ret rn => decide (rn = .lr)
  | .nop => true
  | .bCond _ _ => true
  | .cbz _ _ _ _ => true
  | .tbz _ _ _ _ _ => true
  | .addSubImm _ _ rd _ _ _ => decide (rd ≠ .lr)
  | .addSubShift _ _ rd _ _ _ _ => decide (rd ≠ .lr)
  | .logicalImm _ _ rd _ _ => decide (rd ≠ .lr)
  | .bitfield _ _ rd _ _ _ => decide (rd ≠ .lr)
  | .condCompareImm _ _ _ _ _ _ => true
  | .str _ _ addr => decide (addr.baseReg ≠ .lr)
  | .strSimd _ _ addr => decide (addr.baseReg ≠ .lr)
  | .stpSimd _ _ _ addr => decide (addr.baseReg ≠ .lr)
  | .simdInsDup _ _ _ _ _ rd => decide (Reg.fromZRBits rd ≠ .lr)
  | .sysReg isRead sysreg rt => isRead && decide (sysreg = 0x5807#15) && decide (rt ≠ .lr)
  | .dcZva _ => true
  | _ => false

private theorem readReg64_lr_writeReg64_ne (s : State) {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
    (s.writeReg64 r v).readReg64 .lr = s.readReg64 .lr := by
  cases r with
  | gpr idx =>
    unfold State.writeReg64 State.readReg64 RegFile.read RegFile.write
    have hne : 30#5 ≠ idx := fun h => hr (by subst h; rfl)
    by_cases h31 : idx == 31#5
    · simp [h31]
    · simp [h31, hne]
  | sp => rfl
  | xzr => rfl

private theorem lr_eq_writeReg {s s1 : State} (h : s1.readReg64 .lr = s.readReg64 .lr)
    (w : Width) {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
    (s1.writeReg w r v).readReg64 .lr = s.readReg64 .lr :=
  (readReg64_lr_writeReg64_ne s1 hr _).trans h

private theorem lr_eq_optPState {s s1 : State} (h : s1.readReg64 .lr = s.readReg64 .lr)
    (optPs : Option PState) :
    (match optPs with | some ps => s1.setPState ps | none => s1).readReg64 .lr =
      s.readReg64 .lr := by
  cases optPs <;> exact h

private theorem lr_eq_addrWb {s s1 : State} (s0 : State) (h : s1.readReg64 .lr = s.readReg64 .lr)
    {addr : AddrMode} (hbr : addr.baseReg ≠ .lr) :
    (match (evalAddrMode s0 addr).2 with
      | some (base, newBase) => s1.writeReg64 base newBase
      | none => s1).readReg64 .lr = s.readReg64 .lr := by
  cases addr <;> dsimp only [evalAddrMode, AddrMode.baseReg] at hbr ⊢
  · exact h
  · exact h
  · exact (readReg64_lr_writeReg64_ne s1 hbr _).trans h
  · exact (readReg64_lr_writeReg64_ne s1 hbr _).trans h
  · exact h

private theorem lr_eq_ite {c : Bool} {s t e : State}
    (ht : t.readReg64 .lr = s.readReg64 .lr) (he : e.readReg64 .lr = s.readReg64 .lr) :
    (if c then t else e).readReg64 .lr = s.readReg64 .lr := by
  cases c
  · exact he
  · exact ht

private theorem execInst_lr_of_isBlk21LrPreserving {inst : Instr} {s : State}
    (hsafe : isBlk21LrPreserving inst = true) :
    (execInst inst s).readReg64 .lr = s.readReg64 .lr := by
  cases inst <;> try (unfold isBlk21LrPreserving at hsafe; contradiction)
  case ret rn =>
    unfold isBlk21LrPreserving at hsafe
    have hrn : rn = .lr := of_decide_eq_true hsafe
    subst hrn
    rfl
  case nop => rfl
  case bCond cond relOff =>
    change (if ConditionHolds cond s.pstate then s.setPC (s.pc + relOff) else s.advancePC).readReg64 .lr =
      s.readReg64 .lr
    split <;> rfl
  case cbz w isNonZero rt relOff =>
    let val := s.readReg w rt
    let c := if isNonZero then (val == 0#64) != true else val == 0#64
    change (if c then s.setPC (s.pc + relOff) else s.advancePC).readReg64 .lr = s.readReg64 .lr
    split <;> rfl
  case tbz _ isNonZero rt bit relOff =>
    change (if (s.readReg64 rt).getLsbD bit == isNonZero then s.setPC (s.pc + relOff) else s.advancePC).readReg64 .lr =
      s.readReg64 .lr
    split <;> rfl
  case addSubImm w _ rd _ _ _ =>
    unfold isBlk21LrPreserving at hsafe
    exact lr_eq_optPState (lr_eq_writeReg rfl w (of_decide_eq_true hsafe) _) _
  case addSubShift w _ rd _ _ _ _ =>
    unfold isBlk21LrPreserving at hsafe
    exact lr_eq_optPState (lr_eq_writeReg rfl w (of_decide_eq_true hsafe) _) _
  case logicalImm w _ rd _ _ =>
    unfold isBlk21LrPreserving at hsafe
    exact lr_eq_optPState (lr_eq_writeReg rfl w (of_decide_eq_true hsafe) _) _
  case bitfield w _ rd _ _ _ =>
    unfold isBlk21LrPreserving at hsafe
    exact lr_eq_writeReg rfl w (of_decide_eq_true hsafe) _
  case condCompareImm w isSub rn imm5 nzcv cond =>
    change (execCondCompare w isSub true rn (imm5.zeroExtend 64) .xzr nzcv cond s).readReg64 .lr =
      s.readReg64 .lr
    unfold execCondCompare
    split
    · exact lr_eq_optPState rfl _
    · rfl
  case str sz rt addr =>
    unfold isBlk21LrPreserving at hsafe
    have hbr := of_decide_eq_true hsafe
    change (execStr sz rt addr s).readReg64 .lr = s.readReg64 .lr
    unfold execStr
    split
    · rfl
    · dsimp only []
      split
      · rfl
      · exact lr_eq_addrWb s rfl hbr
  case strSimd sz vt addr =>
    unfold isBlk21LrPreserving at hsafe
    have hbr := of_decide_eq_true hsafe
    have hexec : execInst (.strSimd sz vt addr) s =
        (if !checkAddrSPAligned s addr then s.setStatus (.Exception "SP alignment fault")
         else
           let (ea, wb) := evalAddrMode s addr
           if !s.mem.canWrite ea sz.bytes then s.setStatus (.Exception "permission fault")
           else
             let s1 := s.setMem (s.mem.writeSimdSized sz ea (s.readVReg128 vt))
             let s2 := match wb with | some (base, newBase) => s1.writeReg64 base newBase | none => s1
             s2.advancePC) := rfl
    rw [hexec]
    split
    · rfl
    · dsimp only []
      split
      · rfl
      · exact lr_eq_addrWb s rfl hbr
  case stpSimd sz vt1 vt2 addr =>
    unfold isBlk21LrPreserving at hsafe
    have hbr := of_decide_eq_true hsafe
    clear hsafe
    have hstp (stepBytes : BitVec 64) :
        (if !checkAddrSPAligned s addr then s.setStatus (.Exception "SP alignment fault")
         else
           let (ea, wb) := evalAddrMode s addr
           if !(s.mem.canWrite ea sz.bytes && s.mem.canWrite (ea + stepBytes) sz.bytes) then
             s.setStatus (.Exception "permission fault")
           else
             let v1 := s.readVReg128 vt1
             let v2 := s.readVReg128 vt2
             let m1 := s.mem.writeSimdSized sz ea v1
             let m2 := m1.writeSimdSized sz (ea + stepBytes) v2
             let s1 := s.setMem m2
             let s2 := match wb with | some (base, newBase) => s1.writeReg64 base newBase | none => s1
             s2.advancePC).readReg64 .lr = s.readReg64 .lr :=
      lr_eq_ite rfl (lr_eq_ite rfl (lr_eq_addrWb s rfl hbr))
    cases sz
    · exact hstp 1#64
    · exact hstp 2#64
    · exact hstp 4#64
    · exact hstp 8#64
    · exact hstp 16#64
  case simdInsDup q op imm5 imm4 rn rd =>
    unfold isBlk21LrPreserving at hsafe
    have hrd := of_decide_eq_true hsafe
    clear hsafe
    let esize : Nat :=
      if (imm5.extractLsb' 0 1) == 1#1 then 8
      else if (imm5.extractLsb' 0 2) == 2#2 then 16
      else if (imm5.extractLsb' 0 3) == 4#3 then 32
      else 64
    let dstIdx : Nat :=
      if esize == 8 then imm5.toNat >>> 1
      else if esize == 16 then imm5.toNat >>> 2
      else if esize == 32 then imm5.toNat >>> 3
      else imm5.toNat >>> 4
    let mask : BitVec 128 := (1#128 <<< esize) - 1#128
    have hexec : execInst (.simdInsDup q op imm5 imm4 rn rd) s =
        (if (imm5.extractLsb' 0 4) == 0#4 then
           { s with status := .Exception s!"unsupported AdvSIMD: simdInsDup (q={if q then 1 else 0} op={if op then 1 else 0} imm5={imm5.toNat} imm4={imm4.toNat}) — architecturally UNDEFINED" }
         else if !op && imm4 == 0b0001#4 && !(esize == 64 && !q) then
           let elem := ((s.readReg64 (Reg.fromZRBits rn)).zeroExtend 128) &&& mask
           let res := mapSimdLanes q esize 0#128 (fun _ => elem)
           (s.writeVReg128 rd res).advancePC
         else if !op && imm4 == 0b0000#4 && !(esize == 64 && !q) then
           let elem := getSimdLane (s.readVReg128 rn) esize dstIdx
           let res := mapSimdLanes q esize 0#128 (fun _ => elem)
           (s.writeVReg128 rd res).advancePC
         else if q && !op && imm4 == 0b0011#4 then
           let elem := ((s.readReg64 (Reg.fromZRBits rn)).zeroExtend 128) &&& mask
           let old := s.readVReg128 rd
           let clearMask := ~~~(mask <<< (dstIdx * esize))
           let res := (old &&& clearMask) ||| (elem <<< (dstIdx * esize))
           (s.writeVReg128 rd res).advancePC
         else if !op && imm4 == 0b0111#4 && ((q && esize == 64) || (!q && esize < 64)) then
           let elem := (getSimdLane (s.readVReg128 rn) esize dstIdx).truncate 64
           let w : Width := if q then .W64 else .W32
           (s.writeReg w (Reg.fromZRBits rd) elem).advancePC
         else if !op && imm4 == 0b0101#4 && ((q && esize < 64) || (!q && esize < 32)) then
           let elem := (getSimdLane (s.readVReg128 rn) esize dstIdx).truncate 64
           let signExt :=
             if elem.getLsbD (esize - 1) then elem ||| ~~~((1#64 <<< esize) - 1#64) else elem
           let w : Width := if q then .W64 else .W32
           (s.writeReg w (Reg.fromZRBits rd) signExt).advancePC
         else if q && op then
           let srcIdx : Nat :=
             if esize == 8 then imm4.toNat
             else if esize == 16 then imm4.toNat >>> 1
             else if esize == 32 then imm4.toNat >>> 2
             else imm4.toNat >>> 3
           let elem := getSimdLane (s.readVReg128 rn) esize srcIdx
           let old := s.readVReg128 rd
           let clearMask := ~~~(mask <<< (dstIdx * esize))
           let res := (old &&& clearMask) ||| (elem <<< (dstIdx * esize))
           (s.writeVReg128 rd res).advancePC
         else
           { s with status := .Exception s!"unsupported AdvSIMD: simdInsDup (q={if q then 1 else 0} op={if op then 1 else 0} imm5={imm5.toNat} imm4={imm4.toNat}) — architecturally UNDEFINED" }) := rfl
    rw [hexec]
    exact lr_eq_ite rfl
      (lr_eq_ite rfl
        (lr_eq_ite rfl
          (lr_eq_ite rfl
            (lr_eq_ite (lr_eq_writeReg rfl _ hrd _)
              (lr_eq_ite (lr_eq_writeReg rfl _ hrd _)
                (lr_eq_ite rfl rfl))))))
  case sysReg isRead sysreg rt =>
    unfold isBlk21LrPreserving at hsafe
    simp only [Bool.and_eq_true] at hsafe
    obtain ⟨⟨hisRead, hsr0⟩, hrt0⟩ := hsafe
    have hsr := of_decide_eq_true hsr0
    have hrt := of_decide_eq_true hrt0
    subst hisRead hsr
    have hexec : execInst (.sysReg true 0x5807#15 rt) s = (s.writeReg64 rt 4#64).advancePC := rfl
    rw [hexec]
    exact readReg64_lr_writeReg64_ne s hrt 4#64
  case dcZva rt =>
    have hexec : execInst (.dcZva rt) s =
        (let ea := s.readReg64 rt &&& ~~~63#64
         if !s.mem.canWrite ea 64 then s.setStatus (.Exception "permission fault")
         else (s.setMem (simdStoreRegs .Q128 (fun _ => 0#128) 4 0#5 ea s.mem)).advancePC) := rfl
    rw [hexec]
    dsimp only []
    split <;> rfl

private theorem blk21_fetchMem_safe_lr
    {mmpl : MultiPlacement} {m : Memory} {pc : BitVec 64} {inst : Instr}
    (hkeep : keepMemsetBlk21 mmpl pc = true)
    (hL : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hfm : (mallocngBlockProg mmpl 21 Syscall.standard).fetchMem m pc = some inst)
    (s : State) :
    inst.isSvc0 = false ∧ (execInst inst s).readReg64 .lr = s.readReg64 .lr := by
  have hchk :
      ((List.range 65).all fun k =>
        match VerifiedLibraries.Musl.memsetWordsSym[k]? with
        | some w =>
          match decode w with
          | some i => !i.isSvc0 && isBlk21LrPreserving i
          | none => false
        | none => false) = true := by
    decide +kernel
  have hoff_lt : (pc - mmpl.base 21).toNat < 260 := of_decide_eq_true hkeep
  let off := (pc - mmpl.base 21).toNat
  have hpc_eq : pc = mmpl.base 21 + BitVec.ofNat 64 off := by
    dsimp only [off]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm (mmpl.base 21),
      BitVec.sub_add_cancel]
  have hfm0 := hfm
  unfold Program.fetchMem at hfm0
  have heg : (mallocngBlockProg mmpl 21 Syscall.standard).externAt? pc = none :=
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.mallocngBlockProg21_externAt_none
      mmpl Syscall.standard pc
  simp only [heg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm0
  split at hfm0
  · cases hfm0
  · rename_i hal_neg
    have hal : pc.toNat % 4 = 0 := Classical.not_not.mp hal_neg
    have hbase_al : (mmpl.base 21).toNat % 4 = 0 := hL.aligned
    have hnowrap : (mmpl.base 21).toNat + 260 ≤ 2 ^ 64 := by
      have hnw := hL.no_wrap
      rwa [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays.mallocngBlockProg21_code_length
        mmpl] at hnw
    have hpc_nat : pc.toNat = (mmpl.base 21).toNat + off := by
      rw [hpc_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    let k := off / 4
    have hoff_k : off = 4 * k := by omega
    have hk : k < 65 := by omega
    have hk_len : k < VerifiedLibraries.Musl.memsetWordsSym.length := by
      rw [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.memsetWordsSym_length]
      exact hk
    have hall_k := List.all_eq_true.mp hchk k (List.mem_range.mpr hk)
    rw [List.getElem?_eq_getElem hk_len] at hall_k
    dsimp only [] at hall_k
    let P_sub := mallocngBlockProg mmpl 21 Syscall.standard
    have hrw :=
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.mallocngBlockProg21_hasWords
        mmpl Syscall.standard).2.1 k hk_len
    change P_sub.readWordOff ((mmpl.base 21 - mmpl.base 21).toNat + 4 * k) =
      some VerifiedLibraries.Musl.memsetWordsSym[k] at hrw
    rw [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, ← hoff_k] at hrw
    cases hdec : decode VerifiedLibraries.Musl.memsetWordsSym[k] with
    | none =>
      rw [hdec] at hall_k
      cases hall_k
    | some inst' =>
      rw [hdec] at hall_k
      have hfetch_sub : P_sub.fetch pc = some inst' := by
        unfold Program.fetch
        have hbase_sub : (pc - P_sub.base).toNat = off := rfl
        rw [heg, hbase_sub, hrw]
        exact hdec
      have hfm_sub : P_sub.fetchMem m pc = some inst' := P_sub.fetchMem_of_fetch hL hfetch_sub
      rw [hfm_sub] at hfm
      cases hfm
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall_k
      exact ⟨hall_k.1, execInst_lr_of_isBlk21LrPreserving hall_k.2⟩

private theorem steps_blk21_lr_eq_of_stripPerm
    {mmpl : MultiPlacement} {L : BitVec 64} {wmem : Memory} {z sf' : State}
    (hsteps : Steps (mallocngBlockProg mmpl 21 Syscall.standard) z sf')
    (hrun_sf : sf'.status = .Running)
    (hlr_z : z.readReg64 .lr = L)
    (hCode_z : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded z.mem)
    (hperm_z : z.mem.perm =
      (ProofLib.stripExecOutside (keepMemsetBlk21 mmpl) wmem).perm) :
    sf'.readReg64 .lr = L := by
  induction hsteps with
  | refl _ => exact hlr_z
  | @step s1 s2 s3 h1 hrest ih =>
    have hCode2 : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s2.mem :=
      h1.codeLoaded hCode_z
    cases h1 with
    | halt_unmapped _ _ _ =>
      have heq := ProofLib.Variant.Steps.eq_of_not_running hrest nofun
      rw [heq] at hrun_sf
      exact nomatch hrun_sf
    | extern_fault _ _ _ =>
      have heq := ProofLib.Variant.Steps.eq_of_not_running hrest nofun
      rw [heq] at hrun_sf
      exact nomatch hrun_sf
    | @extern f _ hext _ _ =>
      rw [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.mallocngBlockProg21_externAt_none
        mmpl Syscall.standard s1.pc] at hext
      cases hext
    | @exec inst _ hfm =>
      have hkeep1 : keepMemsetBlk21 mmpl s1.pc = true :=
        keep_true_of_fetchMem_stripExecOutside hperm_z hfm
      obtain ⟨hnsvc0, hlr_eq⟩ := blk21_fetchMem_safe_lr hkeep1 hCode_z hfm s1
      have heval :
          (mallocngBlockProg mmpl 21 Syscall.standard).evalInst inst s1 = execInst inst s1 := by
        cases inst with
        | system isHint imm =>
          cases isHint
          · by_cases himm : imm == 0#16
            · have heq : imm = 0#16 := of_decide_eq_true himm
              subst heq
              simp [Instr.isSvc0] at hnsvc0
            · simp [Program.evalInst, execInst, execInstWithSvc, himm]
          · simp [Program.evalInst, execInst, execInstWithSvc]
        | _ => rfl
      rw [heval] at ih hCode2
      have hperm2 : (execInst inst s1).mem.perm =
          (ProofLib.stripExecOutside (keepMemsetBlk21 mmpl) wmem).perm :=
        (execInst_perm_of_not_isSvc0 hnsvc0 s1).trans hperm_z
      exact ih hrun_sf (hlr_eq.trans hlr_z) hCode2 hperm2

private theorem f3EmptyMemsetGhostHookNarrow_blk20TrapHook (mmpl : MultiPlacement) (L : BitVec 64) :
    Blk20TrapHook L
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow
        mmpl) := by
  classical
  intro w hrun hlr
  rw [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow_eq_narrow]
  by_cases hAct :
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.ActiveRealPre
        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.masterMemsetSpec w
  · have ⟨_, hsp, x, R, hpreM⟩ := hAct
    obtain ⟨_, _, houtM⟩ :=
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1.narrowMemsetGhostHook_master_ok
        mmpl x R w hrun hpreM hsp
    have hretM :
        Returned w
          (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1.narrowMemsetGhostHook
            mmpl w) := by
      rcases houtM with ⟨hret, _, _⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
      · exact hret
      · dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.masterMemsetSpec] at hp
        rw [satisfies_pure_sepConj] at hp
        exact False.elim hp.1
      · dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.masterMemsetSpec] at hp
        rw [satisfies_pure_sepConj] at hp
        exact False.elim hp.1
      · dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.masterMemsetSpec] at hp
        rw [satisfies_pure_sepConj] at hp
        exact False.elim hp.1
    refine Or.inr ⟨hretM.2.2, hretM.1.trans hlr, ?_⟩
    unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1.narrowMemsetGhostHook
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost.memsetGhostHook
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.linkedCallHook
    by_cases hReal :
        ActiveRealRun (keepMemsetBlk21 mmpl) (Program.ofSvc Syscall.standard)
          (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21) w
    · simp only [hAct, hReal, ↓reduceDIte]
      let s1 := w.setPC (mmpl.base 21)
      let s1' := ProofLib.stripS (keepMemsetBlk21 mmpl) s1
      have hs1_pre :
          s1.mem ⊨
            LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.masterMemsetSpec.pre
              x s1 ∗ R := by
        change w.mem ⊨
          LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.masterMemsetSpec.pre
            x (w.setPC (mmpl.base 21)) ∗ R
        rwa [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost.masterMemset_pre_setPC]
      have hs1'_pre :
          s1'.mem ⊨
            LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.masterMemsetSpec.pre
              x s1' ∗ R := by
        have hsat :=
          LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.satisfies_stripExecOutside
            (keepMemsetBlk21 mmpl) hs1_pre
        rwa [← (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost.specStripSInvariant_masterMemset
          (keepMemsetBlk21 mmpl)).pre_eq x s1] at hsat
      obtain ⟨sf', hsteps', hout'⟩ :=
        subroutine_ok_elim_steps_outcome
          (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.subroutine_ok_masterMemset_of_hasWords
            (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.mallocngBlockProg21_externAt_none
              mmpl Syscall.standard)
            (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.mallocngBlockProg21_hasWords
              mmpl Syscall.standard))
          x R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
      have hret' : Returned s1' sf' := by
        rcases hout' with ⟨hret, _, _⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
        · exact hret
        · dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.masterMemsetSpec] at hp
          rw [satisfies_pure_sepConj] at hp
          exact False.elim hp.1
        · dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.masterMemsetSpec] at hp
          rw [satisfies_pure_sepConj] at hp
          exact False.elim hp.1
        · dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.masterMemsetSpec] at hp
          rw [satisfies_pure_sepConj] at hp
          exact False.elim hp.1
      have hstop0' : SubroutineStop w sf' := Or.inl hret'
      have hnhalt' : sf'.status ≠ .Halted := by
        rw [hret'.2.2]; decide
      obtain ⟨sf, huntil, hstop_sf, hsf_eq, _⟩ :=
        LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.stepsUntil_of_stripS_standard
          (P_real := Program.ofSvc Syscall.standard) (s0 := w) rfl rfl (fun _ _ => rfl)
          (fun pc f he =>
            nomatch
              (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.mallocngBlockProg21_externAt_none
                mmpl Syscall.standard pc) ▸ he)
          hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
      have hchoose := Classical.choose_spec hReal.2.2.2
      have hdet : Classical.choose hReal.2.2.2 = sf :=
        StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
      rw [hdet]
      have hlr_sf : sf.readReg64 .lr = sf'.readReg64 .lr :=
        congrArg (fun z => z.readReg64 .lr) hsf_eq.symm
      rw [hlr_sf]
      exact steps_blk21_lr_eq_of_stripPerm hsteps' hret'.2.2 hlr hReal.2.2.1 rfl
    · simp only [hAct, hReal, ↓reduceDIte]
      rw [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost.keepFsTrace_hookMemset_eq]
      exact hlr
  · refine Or.inl ⟨"ghost-hook precondition violated", ?_⟩
    unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1.narrowMemsetGhostHook
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost.memsetGhostHook
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.linkedCallHook
    simp [hAct]

/-- **Concrete `(A2)` mixed-pass `Blk20TrapHook` theorem for all 7 K-narrowed F3 ghosts in
    `h2k_ghFixedK`:**
    Every non-shim ghost hook `f` in `cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none)`
    satisfies `∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f`. -/
theorem h2k_ghFixedK_blk20TrapHook [LibsignalPlacement]
    (mpl : MultiPlacement) {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {sym : String} {f : State → State}
    (hext : cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f)
    (hnoShim : sym ≠ lsRustNoAllocShimSymCli) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f := by
  intro L hL
  by_cases hmc : sym = CryptoVerification.SignalSession.lsMemcpySym
  · subst hmc
    have hsome :
        cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none)
            CryptoVerification.SignalSession.lsMemcpySym =
          some (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow
            mmpl) := by
      simp (config := { decide := true }) only [cliGhostExterns, h2k_ghFixedK, ↓reduceIte]
    rw [hsome] at hext
    injection hext with hfeq
    subst hfeq
    unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow
    rw [f3EmptyMemcpyGhostHook_eq]
    exact blk20TrapHook_memcpyGhostHook emptyStdProg
      (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20) hL
  · by_cases hms : sym = CryptoVerification.SignalSession.lsMemsetSym
    · subst hms
      have hsome :
          cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none)
              CryptoVerification.SignalSession.lsMemsetSym =
            some (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow
              mmpl) := by
        simp (config := { decide := true }) only [cliGhostExterns, h2k_ghFixedK, ↓reduceIte]
      rw [hsome] at hext
      injection hext with hfeq
      subst hfeq
      exact f3EmptyMemsetGhostHookNarrow_blk20TrapHook mmpl L
    · exact blk20TrapHook_of_exception_on_keepLr (h2k_keepSub_covers_blk20 hMm L hL) fun _ hkw =>
        exception_of_keepLr_false_of_noException
          (fun hnoex => h2k_keepSubLr_false_of_noException mpl mmpl hext hnoShim hnoex hms hmc) hkw

/-- `W`-independent narrow (`keepMemcpyBlk20 mmpl`) `memcpy` ghost hook (`h2k_memcpyGhostHookNarrow`). -/
@[expose] noncomputable def h2k_memcpyGhostHookNarrow (mmpl : MultiPlacement) : State → State :=
  f3LinkedCallHook (keepMemcpyBlk20 mmpl) hole2_emptyProg
    (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20)
    (fun _ _ => masterMemcpySpec) hookMemcpy

theorem h2k_memcpyGhostHookNarrow_master_ok (mmpl : MultiPlacement) :
    HookOk (h2k_memcpyGhostHookNarrow mmpl) masterMemcpySpec := by
  change HookOk
    (f3EmptyMemcpyGhostHook (keepMemcpyBlk20 mmpl)
      (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20)) masterMemcpySpec
  rw [f3EmptyMemcpyGhostHook_eq]
  exact memcpyGhostHook_master_ok rfl (mallocngBlockProg20_svc_eq mmpl) (fun _ _ => rfl)
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

theorem h2k_memcpyGhostHookNarrow_blk20TrapHook (mmpl : MultiPlacement) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L (h2k_memcpyGhostHookNarrow mmpl) := by
  intro L hL
  change Blk20TrapHook L
    (f3EmptyMemcpyGhostHook (keepMemcpyBlk20 mmpl)
      (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20))
  rw [f3EmptyMemcpyGhostHook_eq]
  exact blk20TrapHook_memcpyGhostHook emptyStdProg
    (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20) hL

/-- `W`-polymorphic `(A1)` + `(A2)` trap-discharged behind-stub `On` replay for
    `h2k_memcpyGhostHookNarrow`. -/
theorem h2k_memcpyGhostHookNarrow_stub_replayOn_of_trap_ret
    {P_ghost : Program} {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc =
      none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 20))
    {sf : State}
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    let f_mc := h2k_memcpyGhostHookNarrow mmpl
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none ∧
    ∀ u : State,
      Steps P_ghost (f_mc u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f_mc u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f_mc u).mem →
      ExecFrozen u.mem →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f_mc u) ∧
        ExecFrozen (f_mc u).mem ∧
        F3CodeInv mpl mmpl (f_mc u).mem ∧
        (f_mc u).fs = u.fs := by
  have h20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  refine ⟨hreal_stub_none, fun u hrest hpc hrun hnoex hkf hfr hInv => ?_⟩
  have hcl20 : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded u.mem :=
    hInv.mngBlockCodeLoaded 20 h20 (fun _ => none) (fun _ => none) Syscall.standard
  have hlr_false : keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
    blk20_lr_trap_after_hook_ret
      (h2k_memcpyGhostHookNarrow_blk20TrapHook mmpl)
      hblk20_ext
      (hcl20.of_keepsFrozen hkf)
      hrest hrun hrun_sf' hnoex_sf hnhalt_sf
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
    f3LinkedCallHook_empty_visitedIn
      (mallocngBlockProg20_svc_eq mmpl)
      (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
      (subroutine_ok_masterMemcpy_of_hasWords
        (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
        (mallocngBlockProg20_hasWords mmpl Syscall.standard))
      (specStripSInvariant_masterMemcpy (keepMemcpyBlk20 mmpl))
      specPreservesFsTrace_masterMemcpy masterMemcpy_pre_setPC masterMemcpy_outcome_setPC
      hrun hnoex hfr hlr_false
      (codeLoaded_stripExecOutside_blk20 (keepCoversBlk20_keepMemcpyBlk20 mmpl) hcl20)
  have hBody :=
    h2sl_steps_realW_of_visitedIn_keepSub hLs mmpl W
      (stepsVisitedIn_mono (h2k_keepSub_covers_blk20 hMm) hvis)
  have hSteps := (hStub u hpc hrun hfr hInv).trans hBody
  exact ⟨hSteps, hfr_sf, hInv.of_keepsFrozen hSteps.keepsFrozen, hfs_sf⟩

/-! ## 5. Exact Clobber Endpoint (`HookExactMemcpy`) for `h2k_memcpyGhostHook*` -/

/-- Unconditional `HookExactMemcpy` for `h2k_memcpyGhostHookNarrow mmpl` (route (i) narrow ghost
    `memcpy` hook). -/
theorem h2k_memcpyGhostHookNarrow_exact (mmpl : MultiPlacement) :
    HookExactMemcpy (h2k_memcpyGhostHookNarrow mmpl) := by
  change HookExactMemcpy
    (f3EmptyMemcpyGhostHook (keepMemcpyBlk20 mmpl)
      (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20))
  exact f3EmptyMemcpyGhostHook_exact (keepMemcpyBlk20 mmpl)
    (mallocngBlockProg20_svc_eq mmpl)
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

/-- `HookExactMemcpy` for `h2k_memcpyGhostHook mmpl` under `mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem h2k_memcpyGhostHook_exact {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    HookExactMemcpy (h2k_memcpyGhostHook mmpl) := by
  rw [h2k_memcpyGhostHook_eq_f3Empty]
  exact f3EmptyMemcpyGhostHook_exact hole2_keepSub f3TrialRxProg_svc f3TrialRxProg_no_ext
    (h2k_f3TrialRxProg_hasWords_blk20 hMm)

/-- `K`-narrowed (`hole2_keepSub (u.readReg64 .lr) = false`) exactness for `h2k_memcpyGhostHookK mmpl`
    (route (ii) `K`-assembly `memcpy` ghost hook). -/
theorem h2k_memcpyGhostHookK_exact_of_keepLr_false {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State} {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hlr_false : hole2_keepSub (u.readReg64 .lr) = false)
    (hrun : u.status = .Running)
    (hsp : u.spAligned = true)
    (hx0 : u.readReg64 .x0 = dst)
    (hx1 : u.readReg64 .x1 = src)
    (hx2 : (u.readReg64 .x2).toNat = len)
    (hlr : u.readReg64 .lr = lr)
    (hread : u.mem.readBytes src len = bs)
    (hrw : u.mem.RW dst len)
    (hreadable : u.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len) :
    ∃ c : MemcpyClobber,
      h2k_memcpyGhostHookK mmpl u = applyMemcpyClobber u (u.mem.writeBytes dst bs) lr c := by
  rw [h2k_memcpyGhostHookK_eq_f3EmptyK]
  exact f3EmptyMemcpyGhostHookK_exact_of_keepLr_false f3TrialRxProg_svc f3TrialRxProg_no_ext
    (h2k_f3TrialRxProg_hasWords_blk20 hMm)
    hlr_false hrun hsp hx0 hx1 hx2 hlr hread hrw hreadable hdisj

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy
