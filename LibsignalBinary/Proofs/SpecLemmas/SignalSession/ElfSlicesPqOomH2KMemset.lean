/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2 -- proof-setup: allow-public-import
public import ProofLib.ProgramReflection -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import ProofLib.StdStartup.MemOps

/-!
# K-Route `W`-Independent `memset` Ghost Hook Instance (`ElfSlicesPqOomH2KMemset`)

Concrete `CliElfLib`-side K-convention `memset` ghost hook (`rev_c1.md` §4b, Card `H-C6` Task 2),
matching the exact construction of the 7 F3 ghosts in `ElfSlicesPqOomH2KHooks.h2k_ghFixedK`:

1. **`W`-Independent Definitions (`h2k_memsetGhostHook`, `h2k_memsetGhostHookK`)**:
   Built with `f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg (mmpl.base 21)` at
   `(fun _ _ => masterMemsetSpec)` and `(fun _ _ => h2k_withKeepLrFalse hole2_keepSub
   masterMemsetSpec)` with fallback `hookMemset`, plus `rfl` bridges
   `memsetSpecK_eq_h2k_withKeepLrFalse` and `hole2_emptyProg_eq_emptyStdProg`.
2. **Kernel-Checked `f3TrialRxProg.hasWords (mmpl.base 21) memsetWordsSym`**:
   Verified at `f3MallocngMpl` from `f3TrialRxWordTree` (`rfl_kernel`) and transported to any
   `mmpl` satisfying `mallocngLib.LinkedAt cliElfBytes mmpl` via
   `f3CliElf_mallocng_linkedAt_unique`.
3. **Complete Consumer `HookOk` Suite (`hMm` Only, `W`-Independent)**:
   Plain and `h2k_withKeepLrFalse hole2_keepSub`-narrowed `HookOk`, `HookFsTraced`, `VmPreserved`,
   and `OomPreserved ∧ PoolPreserved` contracts requiring only
   `hMm : mallocngLib.LinkedAt cliElfBytes mmpl` (valid both before and after `"memset"` is removed
   from `cliHookTablePlaced`).
4. **`W`-Polymorphic Replays via `h2sl_steps_realW_of_visitedIn_keepSub`**:
   - Target-entry replay (`h2k_memsetGhostHook_target_replay`,
     `h2k_memsetGhostHookK_target_replay`) to `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`
     from `u.setPC (mmpl.base 21)`, closed unconditionally today under `hLs` + `hMm` +
     `F3CodeInv mpl mmpl u.mem`;
   - Behind-stub `StubReachesTargetOn (F3CodeInv mpl mmpl)` replay
     (`h2k_memsetGhostHook_stub_replayOn`, `h2k_memsetGhostHookK_stub_replayOn`) and single-row
     `GhostExternReplaysS` (`h2k_memsetGhostHook_replaysS`, `h2k_memsetGhostHookK_replaysS`) ready
     for the `"memset"` cutover (`h2b2_dehooked_stubReachesTargetOn`).
5. **Route Selection Note (`rev_c6` F1) & Closed Ghost-Side `hblk21_ext` (`rev_c6` F3):**
   - **K route / Option `(ii)`:** use `h2k_memsetGhostHookK` + `h2k_memsetGhostHookK_replaysS`
     (`hole2_keepSub lr = false` comes from `noException`, transfer `keep` can be `fun _ => false`,
     callers prove `HookOk` under `memsetSpecK`).
   - **Option `(i)` / Variant A:** use `h2k_memsetGhostHookNarrow` +
     `h2k_memsetGhostHookNarrow_stub_replayOn_of_trap_ret` (`HookOk` holds unconditionally for all
     callers via `hookMemset` fallback; `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` comes from
     the `(A1)`+`(A2)` trap + `hlr_s0` at Block-617 entry `sm.lr`, with `hblk21_ext` proved
     compositionally via `h2k_cliGhostExterns_ghFixedK_blk21_ext` + `h2k_shimStub_not_in_blk21` or
     at `h2k_ghFixedK` via `ElfSlicesPqOomH2KNarrowR1.h2k_ghFixedK_blk21_ext_trap`).
   - **Plain `h2k_memsetGhostHook` (`keep = hole2_keepSub`):** **not usable for Option `(i)`**
     because its replay requires `hole2_keepSub (u.readReg64 .lr) = false` whereas the `blk21` trap
     only gives `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` (for `lr ∈ hole2_keepSub \ blk21`
     it falls back to `hookMemset` at valid hole code with no trap); `h2k_memsetGhostHookK`
     dominates it on the K route (retained as the internal plain-`HookOk` base).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open ProofLib.StdStartup (checkWordsAt hasWords_of_wordTree)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memsetWordsSym)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (
  sessionMemsetRegionSpec sessionMemsetSpec withStack
)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (session2MemsetExternSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec
)
open CryptoVerification.SignalSession (
  CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsReadFileSym lsReadStdinSym
  lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
  lsRustReallocSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC cliGhostExterns)
open CryptoVerification.SignalSession.CliExt (memsetSpec)
open LibsignalBinary.Heap (OomPreserved PoolPreserved VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (libcMemsetCliSpec memsetRegionCliSpec)
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
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  mallocngBlockProg21_externAt_none mallocngBlockProg21_hasWords
  masterMemsetSpec memsetSpecK
  subroutine_ok_masterMemset_of_hasWords subroutine_ok_masterMemsetK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  keepCoversBlk21_keepMemsetBlk21 keepMemsetBlk21
  masterMemset_outcome_setPC masterMemset_pre_setPC
  masterMemsetK_outcome_setPC masterMemsetK_pre_setPC
  specPreservesFsTrace_masterMemset specPreservesFsTrace_masterMemsetK
  specStripSInvariant_masterMemset specStripSInvariant_masterMemsetK
  withExecFrozen
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays (
  codeLoaded_stripExecOutside_blk21 codeLoaded_stripExecOutside_of_keep
  keepCoversBlk21_keepRange keepRange mallocngBlockProg21_svc_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet (
  Blk21TrapHook blk21TrapHook_memsetGhostHook blk21TrapHook_of_exception_on_keepLr
  blk21_lr_trap_after_hook_ret
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  activeF3CallPre_const_iff emptyStdProg f3EmptyMemsetGhostHook f3EmptyMemsetGhostHookK
  f3EmptyMemsetGhostHook_any_memsetSpecK_ok
  f3EmptyMemsetGhostHook_cliMemset_budget_ok f3EmptyMemsetGhostHook_cliMemset_keepsFs_ok
  f3EmptyMemsetGhostHook_cliMemset_ok f3EmptyMemsetGhostHook_fs f3EmptyMemsetGhostHook_fsT
  f3EmptyMemsetGhostHook_libcMemset_budget_keepsFs_ok f3EmptyMemsetGhostHook_libcMemset_budget_ok
  f3EmptyMemsetGhostHook_libcMemset_execFrozen_ok f3EmptyMemsetGhostHook_libcMemset_keepsFs_ok
  f3EmptyMemsetGhostHook_libcMemset_ok f3EmptyMemsetGhostHook_libcMemsetCli_ok
  f3EmptyMemsetGhostHook_master_ok f3EmptyMemsetGhostHook_memsetRegion_budget_ok
  f3EmptyMemsetGhostHook_memsetRegion_budget_withStack_keepsFs_ok
  f3EmptyMemsetGhostHook_memsetRegion_budget_withStack_ok
  f3EmptyMemsetGhostHook_memsetRegion_execFrozen_ok f3EmptyMemsetGhostHook_memsetRegion_keepsFs_ok
  f3EmptyMemsetGhostHook_memsetRegion_ok f3EmptyMemsetGhostHook_memsetRegion_withStack_ok
  f3EmptyMemsetGhostHook_memsetRegionCli_ok f3EmptyMemsetGhostHook_oomPoolPreserved
  f3EmptyMemsetGhostHook_session2MemsetExtern_budget_keepsFs_ok
  f3EmptyMemsetGhostHook_session2MemsetExtern_budget_ok
  f3EmptyMemsetGhostHook_session2MemsetExtern_execFrozen_ok
  f3EmptyMemsetGhostHook_session2MemsetExtern_keepsFs_ok
  f3EmptyMemsetGhostHook_session2MemsetExtern_ok f3EmptyMemsetGhostHook_sessionMemset_execFrozen_ok
  f3EmptyMemsetGhostHook_sessionMemset_keepsFs_ok f3EmptyMemsetGhostHook_sessionMemset_ok
  f3EmptyMemsetGhostHook_sessionMemsetBudget_keepsFs_ok f3EmptyMemsetGhostHook_sessionMemsetBudget_ok
  f3EmptyMemsetGhostHook_sessionMemsetRegion_execFrozen_ok
  f3EmptyMemsetGhostHook_sessionMemsetRegion_keepsFs_ok f3EmptyMemsetGhostHook_sessionMemsetRegion_ok
  f3EmptyMemsetGhostHook_sessionMemsetRegion_withStack_ok
  f3EmptyMemsetGhostHook_sessionMemsetRegionBudget_ok
  f3EmptyMemsetGhostHook_sessionMemsetRegionBudget_withStack_keepsFs_ok
  f3EmptyMemsetGhostHook_sessionMemsetRegionBudget_withStack_ok
  f3EmptyMemsetGhostHook_trace f3EmptyMemsetGhostHook_vmPreserved
  f3EmptyMemsetGhostHookK_cliMemsetK_budget_ok f3EmptyMemsetGhostHookK_cliMemsetK_keepsFs_ok
  f3EmptyMemsetGhostHookK_cliMemsetK_ok f3EmptyMemsetGhostHookK_fs f3EmptyMemsetGhostHookK_fsT
  f3EmptyMemsetGhostHookK_keepLr_false_of_noException f3EmptyMemsetGhostHookK_libcMemsetCliK_ok
  f3EmptyMemsetGhostHookK_libcMemsetK_budget_keepsFs_ok
  f3EmptyMemsetGhostHookK_libcMemsetK_budget_ok f3EmptyMemsetGhostHookK_libcMemsetK_keepsFs_ok
  f3EmptyMemsetGhostHookK_libcMemsetK_ok f3EmptyMemsetGhostHookK_masterK_ok
  f3EmptyMemsetGhostHookK_memsetRegionCliK_ok f3EmptyMemsetGhostHookK_memsetRegionK_budget_ok
  f3EmptyMemsetGhostHookK_memsetRegionK_budget_withStack_keepsFs_ok
  f3EmptyMemsetGhostHookK_memsetRegionK_budget_withStack_ok
  f3EmptyMemsetGhostHookK_memsetRegionK_keepsFs_ok f3EmptyMemsetGhostHookK_memsetRegionK_ok
  f3EmptyMemsetGhostHookK_oomPoolPreserved
  f3EmptyMemsetGhostHookK_session2MemsetExternK_budget_keepsFs_ok
  f3EmptyMemsetGhostHookK_session2MemsetExternK_budget_ok
  f3EmptyMemsetGhostHookK_session2MemsetExternK_keepsFs_ok
  f3EmptyMemsetGhostHookK_session2MemsetExternK_ok
  f3EmptyMemsetGhostHookK_sessionMemsetBudgetK_keepsFs_ok
  f3EmptyMemsetGhostHookK_sessionMemsetBudgetK_ok
  f3EmptyMemsetGhostHookK_sessionMemsetK_keepsFs_ok f3EmptyMemsetGhostHookK_sessionMemsetK_ok
  f3EmptyMemsetGhostHookK_sessionMemsetRegionBudgetK_ok
  f3EmptyMemsetGhostHookK_sessionMemsetRegionBudgetK_withStack_keepsFs_ok
  f3EmptyMemsetGhostHookK_sessionMemsetRegionBudgetK_withStack_ok
  f3EmptyMemsetGhostHookK_sessionMemsetRegionK_keepsFs_ok
  f3EmptyMemsetGhostHookK_sessionMemsetRegionK_ok
  f3EmptyMemsetGhostHookK_trace f3EmptyMemsetGhostHookK_vmPreserved
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (
  f3LsSymAddrs lsInternedMultiLib lsSharedExterns ls_blockSymsMatch_ok
  ls_idsOk ls_names_nodup ls_sharedExterns_lt ls_toMultiPlacedLib_eq
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced (
  f3CliElf_libsignal_inElf_unique f3CliElf_mallocng_linkedAt_unique f3LsMpl f3TrialElf_parse
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
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2 (
  h2sl_realW_noExtern_keepSub h2sl_steps_realW_of_visitedIn_keepSub
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst (
  hole2_emptyProg hole2_keepSub
)

/-! ## 1. K-Convention `W`-Independent Definitions & Definitional (`rfl`) Bridges -/

/-- `MemsetCode.memsetSpecK` is definitionally identical (`rfl`) to
    `ElfSlicesPqOomH2KHooks.h2k_withKeepLrFalse`. -/
theorem memsetSpecK_eq_h2k_withKeepLrFalse {α : Type} (keep : BitVec 64 → Bool) (spec : Spec α) :
    memsetSpecK keep spec = h2k_withKeepLrFalse keep spec := rfl

/-- `ElfSlicesPqOomPlacedInst.hole2_emptyProg` is definitionally identical (`rfl`) to
    `MemsetGhostK.emptyStdProg` (`Program.ofSvc Syscall.standard`). -/
theorem hole2_emptyProg_eq_emptyStdProg :
    hole2_emptyProg = emptyStdProg := rfl

/-- `hole2_keepSub` equals `keepRange f3RxSegBase.toNat (f3RxSegBase.toNat + 4 * f3RxWordCount)`
    (`rev_c1.md` §4 nice-to-have #4, stated purely symbolically via `f3RxSegBase` and
    `f3RxWordCount`). -/
theorem hole2_keepSub_eq_keepRange_f3Rx :
    hole2_keepSub =
      keepRange f3RxSegBase.toNat (f3RxSegBase.toNat + 4 * f3RxWordCount) := by
  change keepRange _ _ = keepRange f3RxSegBase.toNat (f3RxSegBase.toNat + 4 * f3RxWordCount)
  exact congrArg₂ keepRange (by decide) (by decide)

/-- **Plain `W`-independent K-convention `memset` ghost hook (`h2k_memsetGhostHook`):**
    Instantiates `f3LinkedCallHook` with `hole2_keepSub`, `hole2_emptyProg`, `f3TrialRxProg`, and
    `entryTarget := mmpl.base 21`.
    *Route note (`rev_c6` F1):* Retained as the plain-`HookOk` base forwarded by
    `h2k_memsetGhostHookK`; **do not use for Option `(i)` / Variant A**, because its replay needs
    `hole2_keepSub (u.readReg64 .lr) = false` whereas the `blk21` trap only gives
    `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` (`h2k_memsetGhostHookK` dominates it on the K
    route, and `h2k_memsetGhostHookNarrow` is the Option `(i)` hook). -/
@[expose] noncomputable def h2k_memsetGhostHook (mmpl : MultiPlacement) : State → State :=
  f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg (mmpl.base 21)
    (fun _ _ => masterMemsetSpec) hookMemset

/-- **`K`-narrowed `W`-independent K-convention `memset` ghost hook (`h2k_memsetGhostHookK`):**
    Instantiates `f3LinkedCallHook` with `h2k_withKeepLrFalse hole2_keepSub masterMemsetSpec`,
    matching `h2k_ghFixedK` (`ElfSlicesPqOomH2KHooks.lean:559`) verbatim.
    *Route note (`rev_c6` F1):* Use this hook + `h2k_memsetGhostHookK_replaysS` for the K route /
    Option `(ii)` (`hole2_keepSub lr = false` comes from `noException`, transfer `keep := fun _ =>
    false`, callers prove `HookOk` under `memsetSpecK`). -/
@[expose] noncomputable def h2k_memsetGhostHookK (mmpl : MultiPlacement) : State → State :=
  f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg (mmpl.base 21)
    (fun _ _ => h2k_withKeepLrFalse hole2_keepSub masterMemsetSpec) hookMemset

theorem h2k_memsetGhostHook_eq_f3Empty (mmpl : MultiPlacement) :
    h2k_memsetGhostHook mmpl =
      f3EmptyMemsetGhostHook hole2_keepSub f3TrialRxProg (mmpl.base 21) := rfl

theorem h2k_memsetGhostHookK_eq_f3EmptyK (mmpl : MultiPlacement) :
    h2k_memsetGhostHookK mmpl =
      f3EmptyMemsetGhostHookK hole2_keepSub f3TrialRxProg (mmpl.base 21) := rfl

/-! ## 2. Kernel-Checked `f3TrialRxProg.hasWords (mmpl.base 21) memsetWordsSym` & `CodeLoaded` -/

private theorem memsetWordsSym_len_le : memsetWordsSym.length ≤ 1024 :=
  Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memsetWordsSym.length 1024 = true)

set_option maxRecDepth 4000000 in
private theorem h2k_f3Trial_blk21_chk :
    checkWordsAt f3TrialRxWordTree
      (f3MallocngMpl.base 21 - f3RxSegBase).toNat memsetWordsSym = true := by
  rfl_kernel

/-- Unconditional kernel-checked `hasWords` for `memsetWordsSym` at `f3MallocngMpl.base 21` inside
    `f3TrialRxProg`. -/
theorem h2k_f3TrialRxProg_hasWords_blk21_f3 :
    f3TrialRxProg.hasWords (f3MallocngMpl.base 21) memsetWordsSym := by
  have hoff_lt : (f3MallocngMpl.base 21 - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen := memsetWordsSym_len_le
  exact hasWords_of_wordTree f3RxWordCount
    f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by omega)
    f3TrialRxProg_stubs f3TrialRxProg_symbols h2k_f3Trial_blk21_chk

/-- `f3TrialRxProg` holds `memsetWordsSym` at `mmpl.base 21` for every `mmpl` satisfying
    `mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem h2k_f3TrialRxProg_hasWords_blk21 {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    f3TrialRxProg.hasWords (mmpl.base 21) memsetWordsSym := by
  have h21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  have hbase : mmpl.base 21 = f3MallocngMpl.base 21 :=
    (f3CliElf_mallocng_linkedAt_unique hMm).1 21 h21
  rw [hbase]
  exact h2k_f3TrialRxProg_hasWords_blk21_f3

/-- `F3CodeInv mpl mmpl m` implies `f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub m)`. -/
theorem h2k_f3CodeInv_rxProg_keepSub {mpl mmpl : MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub m) := by
  have hlen : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
    rw [f3TrialRxWordTree_eq]
    exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size
  have hnw : f3RxSegBase.toNat + 4 * f3RxWordCount ≤ 2 ^ 64 := by decide
  refine codeLoaded_stripExecOutside_of_keep (fun off hoff => ?_) hInv.rxCode
  rw [hlen] at hoff
  rw [hole2_keepSub_eq_keepRange_f3Rx, f3TrialRxProg_base]
  unfold keepRange
  have hadd : (f3RxSegBase + BitVec.ofNat 64 off).toNat = f3RxSegBase.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hadd, decide_eq_true_eq]
  omega

/-! ## 3. State / Frame / Consumer `HookOk` Suite (`hMm` Only, `W`-Independent) -/

theorem h2k_memsetGhostHook_fs (mmpl : MultiPlacement) (s0 : State) :
    (h2k_memsetGhostHook mmpl s0).fs = s0.fs :=
  f3EmptyMemsetGhostHook_fs hole2_keepSub f3TrialRxProg (mmpl.base 21) s0

theorem h2k_memsetGhostHookK_fs (mmpl : MultiPlacement) (s0 : State) :
    (h2k_memsetGhostHookK mmpl s0).fs = s0.fs :=
  f3EmptyMemsetGhostHookK_fs hole2_keepSub f3TrialRxProg (mmpl.base 21) s0

theorem h2k_memsetGhostHook_fsT (mmpl : MultiPlacement) :
    HookFsTraced IsFsC (h2k_memsetGhostHook mmpl) :=
  f3EmptyMemsetGhostHook_fsT hole2_keepSub f3TrialRxProg (mmpl.base 21)

theorem h2k_memsetGhostHookK_fsT (mmpl : MultiPlacement) :
    HookFsTraced IsFsC (h2k_memsetGhostHookK mmpl) :=
  f3EmptyMemsetGhostHookK_fsT hole2_keepSub f3TrialRxProg (mmpl.base 21)

theorem h2k_memsetGhostHookK_keepLr_false_of_noException
    {mmpl : MultiPlacement} {u : State}
    (hnoex : ∀ msg, (h2k_memsetGhostHookK mmpl u).status ≠ .Exception msg) :
    hole2_keepSub (u.readReg64 .lr) = false :=
  f3EmptyMemsetGhostHookK_keepLr_false_of_noException hnoex

section ConsumerContracts

variable {mmpl : MultiPlacement} (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
include hMm

private theorem hw_blk21 : f3TrialRxProg.hasWords (mmpl.base 21) memsetWordsSym :=
  h2k_f3TrialRxProg_hasWords_blk21 hMm

theorem h2k_memsetGhostHook_trace (s0 : State) :
    (h2k_memsetGhostHook mmpl s0).trace = s0.trace :=
  f3EmptyMemsetGhostHook_trace f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) s0

theorem h2k_memsetGhostHookK_trace (s0 : State) :
    (h2k_memsetGhostHookK mmpl s0).trace = s0.trace :=
  f3EmptyMemsetGhostHookK_trace f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) s0

theorem h2k_memsetGhostHook_vmPreserved (s0 : State) :
    VmPreserved s0 (h2k_memsetGhostHook mmpl s0) :=
  f3EmptyMemsetGhostHook_vmPreserved f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) s0

theorem h2k_memsetGhostHookK_vmPreserved (s0 : State) :
    VmPreserved s0 (h2k_memsetGhostHookK mmpl s0) :=
  f3EmptyMemsetGhostHookK_vmPreserved f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) s0

theorem h2k_memsetGhostHook_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (h2k_memsetGhostHook mmpl s0) ∧
    PoolPreserved s0 (h2k_memsetGhostHook mmpl s0) :=
  f3EmptyMemsetGhostHook_oomPoolPreserved f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) s0

theorem h2k_memsetGhostHookK_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (h2k_memsetGhostHookK mmpl s0) ∧
    PoolPreserved s0 (h2k_memsetGhostHookK mmpl s0) :=
  f3EmptyMemsetGhostHookK_oomPoolPreserved f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) s0

theorem h2k_memsetGhostHook_master_ok : HookOk (h2k_memsetGhostHook mmpl) masterMemsetSpec :=
  f3EmptyMemsetGhostHook_master_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_masterK_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub masterMemsetSpec) :=
  f3EmptyMemsetGhostHookK_masterK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_libcMemset_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (libcMemsetSpec stk) :=
  f3EmptyMemsetGhostHook_libcMemset_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_sessionMemset_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (sessionMemsetSpec stk) :=
  f3EmptyMemsetGhostHook_sessionMemset_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_cliMemset_ok : HookOk (h2k_memsetGhostHook mmpl) memsetSpec :=
  f3EmptyMemsetGhostHook_cliMemset_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_memsetRegion_ok : HookOk (h2k_memsetGhostHook mmpl) memsetRegionSpec :=
  f3EmptyMemsetGhostHook_memsetRegion_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_sessionMemsetRegion_ok :
    HookOk (h2k_memsetGhostHook mmpl) sessionMemsetRegionSpec :=
  f3EmptyMemsetGhostHook_sessionMemsetRegion_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_session2MemsetExtern_ok (stk : Nat := 16384) :
    HookOk (h2k_memsetGhostHook mmpl) (session2MemsetExternSpec stk) :=
  f3EmptyMemsetGhostHook_session2MemsetExtern_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_libcMemset_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (libcMemsetSpec stk).keepsFs :=
  f3EmptyMemsetGhostHook_libcMemset_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_sessionMemset_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (sessionMemsetSpec stk).keepsFs :=
  f3EmptyMemsetGhostHook_sessionMemset_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_cliMemset_keepsFs_ok :
    HookOk (h2k_memsetGhostHook mmpl) memsetSpec.keepsFs :=
  f3EmptyMemsetGhostHook_cliMemset_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_memsetRegion_keepsFs_ok :
    HookOk (h2k_memsetGhostHook mmpl) memsetRegionSpec.keepsFs :=
  f3EmptyMemsetGhostHook_memsetRegion_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_sessionMemsetRegion_keepsFs_ok :
    HookOk (h2k_memsetGhostHook mmpl) sessionMemsetRegionSpec.keepsFs :=
  f3EmptyMemsetGhostHook_sessionMemsetRegion_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_session2MemsetExtern_keepsFs_ok (stk : Nat := 16384) :
    HookOk (h2k_memsetGhostHook mmpl) (session2MemsetExternSpec stk).keepsFs :=
  f3EmptyMemsetGhostHook_session2MemsetExtern_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_memsetRegion_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (withStack memsetRegionSpec stk) :=
  f3EmptyMemsetGhostHook_memsetRegion_withStack_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_sessionMemsetRegion_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (withStack sessionMemsetRegionSpec stk) :=
  f3EmptyMemsetGhostHook_sessionMemsetRegion_withStack_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_libcMemset_budget_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (withVmPreserved (libcMemsetSpec stk)) :=
  f3EmptyMemsetGhostHook_libcMemset_budget_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_libcMemset_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (withVmPreserved (libcMemsetSpec stk)).keepsFs :=
  f3EmptyMemsetGhostHook_libcMemset_budget_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_sessionMemsetBudget_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (sessionMemsetBudgetSpec stk) :=
  f3EmptyMemsetGhostHook_sessionMemsetBudget_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_sessionMemsetBudget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (sessionMemsetBudgetSpec stk).keepsFs :=
  f3EmptyMemsetGhostHook_sessionMemsetBudget_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_cliMemset_budget_ok :
    HookOk (h2k_memsetGhostHook mmpl) (withVmPreserved memsetSpec) :=
  f3EmptyMemsetGhostHook_cliMemset_budget_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_session2MemsetExtern_budget_ok (stk : Nat := 16384) :
    HookOk (h2k_memsetGhostHook mmpl) (withVmPreserved (session2MemsetExternSpec stk)) :=
  f3EmptyMemsetGhostHook_session2MemsetExtern_budget_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_session2MemsetExtern_budget_keepsFs_ok (stk : Nat := 16384) :
    HookOk (h2k_memsetGhostHook mmpl) (withVmPreserved (session2MemsetExternSpec stk)).keepsFs :=
  f3EmptyMemsetGhostHook_session2MemsetExtern_budget_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_memsetRegion_budget_ok :
    HookOk (h2k_memsetGhostHook mmpl) (withVmPreserved memsetRegionSpec) :=
  f3EmptyMemsetGhostHook_memsetRegion_budget_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_memsetRegion_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (withStack (withVmPreserved memsetRegionSpec) stk) :=
  f3EmptyMemsetGhostHook_memsetRegion_budget_withStack_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_memsetRegion_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs :=
  f3EmptyMemsetGhostHook_memsetRegion_budget_withStack_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_sessionMemsetRegionBudget_ok :
    HookOk (h2k_memsetGhostHook mmpl) sessionMemsetRegionBudgetSpec :=
  f3EmptyMemsetGhostHook_sessionMemsetRegionBudget_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_sessionMemsetRegionBudget_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (withStack sessionMemsetRegionBudgetSpec stk) :=
  f3EmptyMemsetGhostHook_sessionMemsetRegionBudget_withStack_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_sessionMemsetRegionBudget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (withStack sessionMemsetRegionBudgetSpec stk).keepsFs :=
  f3EmptyMemsetGhostHook_sessionMemsetRegionBudget_withStack_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_memsetRegionCli_ok :
    HookOk (h2k_memsetGhostHook mmpl) memsetRegionCliSpec :=
  f3EmptyMemsetGhostHook_memsetRegionCli_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_libcMemsetCli_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (libcMemsetCliSpec stk) :=
  f3EmptyMemsetGhostHook_libcMemsetCli_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_libcMemset_execFrozen_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (withExecFrozen (libcMemsetSpec stk)) :=
  f3EmptyMemsetGhostHook_libcMemset_execFrozen_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_sessionMemset_execFrozen_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHook mmpl) (withExecFrozen (sessionMemsetSpec stk)) :=
  f3EmptyMemsetGhostHook_sessionMemset_execFrozen_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHook_memsetRegion_execFrozen_ok :
    HookOk (h2k_memsetGhostHook mmpl) (withExecFrozen memsetRegionSpec) :=
  f3EmptyMemsetGhostHook_memsetRegion_execFrozen_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_sessionMemsetRegion_execFrozen_ok :
    HookOk (h2k_memsetGhostHook mmpl) (withExecFrozen sessionMemsetRegionSpec) :=
  f3EmptyMemsetGhostHook_sessionMemsetRegion_execFrozen_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHook_session2MemsetExtern_execFrozen_ok (stk : Nat := 16384) :
    HookOk (h2k_memsetGhostHook mmpl) (withExecFrozen (session2MemsetExternSpec stk)) :=
  f3EmptyMemsetGhostHook_session2MemsetExtern_execFrozen_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

omit hMm in
/-- Any plain `HookOk` on `h2k_memsetGhostHook mmpl` lifts immediately to
    `h2k_withKeepLrFalse hole2_keepSub spec`. -/
theorem h2k_memsetGhostHook_any_withKeepLrFalse_ok {α : Type} {spec : Spec α}
    (hok : HookOk (h2k_memsetGhostHook mmpl) spec) :
    HookOk (h2k_memsetGhostHook mmpl) (h2k_withKeepLrFalse hole2_keepSub spec) :=
  f3EmptyMemsetGhostHook_any_memsetSpecK_ok hok

theorem h2k_memsetGhostHookK_libcMemsetK_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (libcMemsetSpec stk)) :=
  f3EmptyMemsetGhostHookK_libcMemsetK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_sessionMemsetK_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (sessionMemsetSpec stk)) :=
  f3EmptyMemsetGhostHookK_sessionMemsetK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_cliMemsetK_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub memsetSpec) :=
  f3EmptyMemsetGhostHookK_cliMemsetK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_memsetRegionK_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub memsetRegionSpec) :=
  f3EmptyMemsetGhostHookK_memsetRegionK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_sessionMemsetRegionK_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub sessionMemsetRegionSpec) :=
  f3EmptyMemsetGhostHookK_sessionMemsetRegionK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_libcMemsetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (libcMemsetSpec stk).keepsFs) :=
  f3EmptyMemsetGhostHookK_libcMemsetK_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_sessionMemsetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (sessionMemsetSpec stk).keepsFs) :=
  f3EmptyMemsetGhostHookK_sessionMemsetK_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_cliMemsetK_keepsFs_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub memsetSpec.keepsFs) :=
  f3EmptyMemsetGhostHookK_cliMemsetK_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_memsetRegionK_keepsFs_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub memsetRegionSpec.keepsFs) :=
  f3EmptyMemsetGhostHookK_memsetRegionK_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_sessionMemsetRegionK_keepsFs_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub sessionMemsetRegionSpec.keepsFs) :=
  f3EmptyMemsetGhostHookK_sessionMemsetRegionK_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_libcMemsetK_budget_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved (libcMemsetSpec stk))) :=
  f3EmptyMemsetGhostHookK_libcMemsetK_budget_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_libcMemsetK_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved (libcMemsetSpec stk)).keepsFs) :=
  f3EmptyMemsetGhostHookK_libcMemsetK_budget_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_sessionMemsetBudgetK_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (sessionMemsetBudgetSpec stk)) :=
  f3EmptyMemsetGhostHookK_sessionMemsetBudgetK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_sessionMemsetBudgetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (sessionMemsetBudgetSpec stk).keepsFs) :=
  f3EmptyMemsetGhostHookK_sessionMemsetBudgetK_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_cliMemsetK_budget_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved memsetSpec)) :=
  f3EmptyMemsetGhostHookK_cliMemsetK_budget_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_memsetRegionK_budget_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved memsetRegionSpec)) :=
  f3EmptyMemsetGhostHookK_memsetRegionK_budget_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_memsetRegionK_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (withStack (withVmPreserved memsetRegionSpec) stk)) :=
  f3EmptyMemsetGhostHookK_memsetRegionK_budget_withStack_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_memsetRegionK_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs) :=
  f3EmptyMemsetGhostHookK_memsetRegionK_budget_withStack_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_sessionMemsetRegionBudgetK_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub sessionMemsetRegionBudgetSpec) :=
  f3EmptyMemsetGhostHookK_sessionMemsetRegionBudgetK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_sessionMemsetRegionBudgetK_withStack_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (withStack sessionMemsetRegionBudgetSpec stk)) :=
  f3EmptyMemsetGhostHookK_sessionMemsetRegionBudgetK_withStack_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_sessionMemsetRegionBudgetK_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (withStack sessionMemsetRegionBudgetSpec stk).keepsFs) :=
  f3EmptyMemsetGhostHookK_sessionMemsetRegionBudgetK_withStack_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_memsetRegionCliK_ok :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub memsetRegionCliSpec) :=
  f3EmptyMemsetGhostHookK_memsetRegionCliK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm)

theorem h2k_memsetGhostHookK_libcMemsetCliK_ok (stk : Nat := 4096) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (libcMemsetCliSpec stk)) :=
  f3EmptyMemsetGhostHookK_libcMemsetCliK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_session2MemsetExternK_ok (stk : Nat := 16384) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (session2MemsetExternSpec stk)) :=
  f3EmptyMemsetGhostHookK_session2MemsetExternK_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_session2MemsetExternK_keepsFs_ok (stk : Nat := 16384) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (session2MemsetExternSpec stk).keepsFs) :=
  f3EmptyMemsetGhostHookK_session2MemsetExternK_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_session2MemsetExternK_budget_ok (stk : Nat := 16384) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved (session2MemsetExternSpec stk))) :=
  f3EmptyMemsetGhostHookK_session2MemsetExternK_budget_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

theorem h2k_memsetGhostHookK_session2MemsetExternK_budget_keepsFs_ok (stk : Nat := 16384) :
    HookOk (h2k_memsetGhostHookK mmpl) (h2k_withKeepLrFalse hole2_keepSub (withVmPreserved (session2MemsetExternSpec stk)).keepsFs) :=
  f3EmptyMemsetGhostHookK_session2MemsetExternK_budget_keepsFs_ok f3TrialRxProg_svc f3TrialRxProg_no_ext (hw_blk21 hMm) stk

end ConsumerContracts

/-! ## 4. `W`-Polymorphic Replays via `h2sl_steps_realW_of_visitedIn_keepSub` -/

private theorem stepsVisitedIn_mono {D1 D2 : BitVec 64 → Bool} {P1 : Program} {s sf : State}
    (h : ∀ pc, D1 pc = true → D2 pc = true)
    (hvis : h2fsgen_StepsVisitedIn D1 P1 s sf) :
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

/-- **Target-entry `W`-polymorphic replay for `h2k_memsetGhostHook`:**
    Replays `h2k_memsetGhostHook mmpl u` (`P_real := hole2_emptyProg`) into real machine steps on
    `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` starting at `u.setPC (mmpl.base 21)` for
    **every `W : CliHooks`** via `h2sl_steps_realW_of_visitedIn_keepSub` under `hLs`, `hMm`, and
    `F3CodeInv mpl mmpl u.mem`. -/
theorem h2k_memsetGhostHook_target_replay {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (W : CliHooks) {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (h2k_memsetGhostHook mmpl u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (mmpl.base 21)) (h2k_memsetGhostHook mmpl u) ∧
      ExecFrozen (h2k_memsetGhostHook mmpl u).mem ∧
      F3CodeInv mpl mmpl (h2k_memsetGhostHook mmpl u).mem ∧
      (h2k_memsetGhostHook mmpl u).fs = u.fs := by
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
    f3LinkedCallHook_empty_visitedIn f3TrialRxProg_svc f3TrialRxProg_no_ext
      (subroutine_ok_masterMemset_of_hasWords f3TrialRxProg_no_ext
        (h2k_f3TrialRxProg_hasWords_blk21 hMm))
      (specStripSInvariant_masterMemset hole2_keepSub) specPreservesFsTrace_masterMemset
      masterMemset_pre_setPC masterMemset_outcome_setPC hrun hnoex hFr hlr_out
      (h2k_f3CodeInv_rxProg_keepSub hInv)
  have hSteps := h2sl_steps_realW_of_visitedIn_keepSub hLs mmpl W hvis
  exact ⟨hSteps, hfr_sf, hInv.of_keepsFrozen hSteps.keepsFrozen, hfs_sf⟩

/-- **Target-entry `W`-polymorphic replay for `h2k_memsetGhostHookK` (zero caller `lr`
    hypothesis):** discharges `hole2_keepSub (u.readReg64 .lr) = false` automatically from `hnoex`. -/
theorem h2k_memsetGhostHookK_target_replay {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (W : CliHooks) {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (h2k_memsetGhostHookK mmpl u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (mmpl.base 21)) (h2k_memsetGhostHookK mmpl u) ∧
      ExecFrozen (h2k_memsetGhostHookK mmpl u).mem ∧
      F3CodeInv mpl mmpl (h2k_memsetGhostHookK mmpl u).mem ∧
      (h2k_memsetGhostHookK mmpl u).fs = u.fs := by
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
    f3LinkedCallHook_empty_visitedIn f3TrialRxProg_svc f3TrialRxProg_no_ext
      (subroutine_ok_masterMemsetK_of_hasWords hole2_keepSub f3TrialRxProg_no_ext
        (h2k_f3TrialRxProg_hasWords_blk21 hMm))
      (specStripSInvariant_masterMemsetK hole2_keepSub)
      (specPreservesFsTrace_masterMemsetK hole2_keepSub)
      (masterMemsetK_pre_setPC hole2_keepSub) (masterMemsetK_outcome_setPC hole2_keepSub)
      hrun hnoex hFr (f3EmptyMemsetGhostHookK_keepLr_false_of_noException hnoex)
      (h2k_f3CodeInv_rxProg_keepSub hInv)
  have hSteps := h2sl_steps_realW_of_visitedIn_keepSub hLs mmpl W hvis
  exact ⟨hSteps, hfr_sf, hInv.of_keepsFrozen hSteps.keepsFrozen, hfs_sf⟩

/-- **Behind-stub `W`-polymorphic guarded `On` replay for `h2k_memsetGhostHook`:**
    Composes `StubReachesTargetOn (F3CodeInv mpl mmpl)` with
    `h2sl_steps_realW_of_visitedIn_keepSub` across all `W : CliHooks`. -/
theorem h2k_memsetGhostHook_stub_replayOn {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (W : CliHooks)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 21)) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (h2k_memsetGhostHook mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem → hole2_keepSub (u.readReg64 .lr) = false → F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (h2k_memsetGhostHook mmpl u) ∧
        ExecFrozen (h2k_memsetGhostHook mmpl u).mem ∧
        F3CodeInv mpl mmpl (h2k_memsetGhostHook mmpl u).mem ∧
        (h2k_memsetGhostHook mmpl u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hInv => ?_⟩
  obtain ⟨hBody, hfr_sf, hInv_sf, hfs_sf⟩ :=
    h2k_memsetGhostHook_target_replay hLs hMm W hrun hnoex hfr hlr hInv
  exact ⟨(hStub u hpc hrun hfr hInv).trans hBody, hfr_sf, hInv_sf, hfs_sf⟩

/-- **Behind-stub `W`-polymorphic guarded `On` replay for `h2k_memsetGhostHookK` (zero caller `lr`
    hypothesis!):** K-route / Option `(ii)` per-PC replay helper (`rev_c6` F1/F2) for multi-row
    `GhostExternReplaysS` / `GhostExternReplaysOn` passes alongside `h2k_ghFixedK`. -/
theorem h2k_memsetGhostHookK_stub_replayOn {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (W : CliHooks)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 21)) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (h2k_memsetGhostHookK mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem → F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (h2k_memsetGhostHookK mmpl u) ∧
        ExecFrozen (h2k_memsetGhostHookK mmpl u).mem ∧
        F3CodeInv mpl mmpl (h2k_memsetGhostHookK mmpl u).mem ∧
        (h2k_memsetGhostHookK mmpl u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hInv => ?_⟩
  obtain ⟨hBody, hfr_sf, hInv_sf, hfs_sf⟩ :=
    h2k_memsetGhostHookK_target_replay hLs hMm W hrun hnoex hfr hInv
  exact ⟨(hStub u hpc hrun hfr hInv).trans hBody, hfr_sf, hInv_sf, hfs_sf⟩

/-- **Single-row `GhostExternReplaysS` for `h2k_memsetGhostHook`:**
    Single-stub (`hother`) packager; for the multi-row K CLI pass, compose
    `h2k_memsetGhostHookK_stub_replayOn` per PC (`rev_c6` F1/F2). -/
theorem h2k_memsetGhostHook_replaysS {P_ghost : Program} {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (W : CliHooks)
    (hghost_stub : P_ghost.externAt? stubPc = some (h2k_memsetGhostHook mmpl))
    (hother : ∀ pc, pc ≠ stubPc →
      P_ghost.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    (hreal_fr : ∀ pc f,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 21)) :
    GhostExternReplaysS hole2_keepSub (fun u => F3CodeInv mpl mmpl u.mem) P_ghost
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) := by
  have hRep := h2k_memsetGhostHook_stub_replayOn hLs hMm W hreal_stub_none hStub
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hInv => ⟨hreal_fr pc f hr u hrun hfr, hInv.of_keepsFrozen hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hInv =>
      let ⟨hs, hfr', hInv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hInv
      ⟨hs, hfr', hInv'⟩⟩

/-- **Single-row `GhostExternReplaysS` for `h2k_memsetGhostHookK` (polymorphic in `keep_any`!):**
    Discharges `hole2_keepSub (u.readReg64 .lr) = false` internally from `hnoex`. Single-stub
    (`hother`) packager; for the 8-row K CLI pass alongside `h2k_ghFixedK`, plug
    `h2k_memsetGhostHookK_stub_replayOn` directly into the per-PC case split (`rev_c6` F2). -/
theorem h2k_memsetGhostHookK_replaysS (keep_any : BitVec 64 → Bool)
    {P_ghost : Program} {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (W : CliHooks)
    (hghost_stub : P_ghost.externAt? stubPc = some (h2k_memsetGhostHookK mmpl))
    (hother : ∀ pc, pc ≠ stubPc →
      P_ghost.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    (hreal_fr : ∀ pc f,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 21)) :
    GhostExternReplaysS keep_any (fun u => F3CodeInv mpl mmpl u.mem) P_ghost
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) := by
  have hRep := h2k_memsetGhostHookK_stub_replayOn hLs hMm W hreal_stub_none hStub
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hInv => ⟨hreal_fr pc f hr u hrun hfr, hInv.of_keepsFrozen hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hInv =>
      let ⟨hs, hfr', hInv', _⟩ := hRep.2 u hpc hrun hnoex hfr hInv
      ⟨hs, hfr', hInv'⟩⟩

/-! ## 5. `(A2)` `Blk21TrapHook` Coverage for `hole2_keepSub`, `h2k_memsetGhostHook*`, & All 7 Ghosts in `h2k_ghFixedK` -/

/-- `hole2_keepSub` covers `keepMemsetBlk21 mmpl` (`260` B at `mmpl.base 21`) for every `mmpl`
    satisfying `mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem h2k_keepSub_covers_blk21 {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, keepMemsetBlk21 mmpl a = true → hole2_keepSub a = true := by
  have h21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  have hbase : mmpl.base 21 = f3MallocngMpl.base 21 :=
    (f3CliElf_mallocng_linkedAt_unique hMm).1 21 h21
  have hcov_f3 : ∀ off : Nat, off < 260 →
      hole2_keepSub (f3MallocngMpl.base 21 + BitVec.ofNat 64 off) = true := by
    rw [hole2_keepSub_eq_keepRange_f3Rx]
    exact keepCoversBlk21_keepRange f3RxSegBase.toNat (f3RxSegBase.toNat + 4 * f3RxWordCount)
      (by decide) (by decide) (by decide)
  intro a hka
  have hoff_lt : (a - mmpl.base 21).toNat < 260 := of_decide_eq_true hka
  have ha_eq : a = f3MallocngMpl.base 21 + BitVec.ofNat 64 (a - mmpl.base 21).toNat := by
    rw [← hbase, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm (mmpl.base 21),
      BitVec.sub_add_cancel]
  rw [ha_eq]
  exact hcov_f3 _ hoff_lt

/-- Contrapositive helper: if any non-`.Exception` evaluation of `f` forces
    `keep (w.readReg64 .lr) = false`, then `keep (w.readReg64 .lr) = true` forces `(f w).status`
    to be `.Exception msg` for some `msg`. -/
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

/-- Plain `h2k_memsetGhostHook mmpl` satisfies `Blk21TrapHook L` for every `L ∈ blk21`. -/
theorem h2k_memsetGhostHook_blk21TrapHook {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L (h2k_memsetGhostHook mmpl) := by
  intro L hL
  rw [h2k_memsetGhostHook_eq_f3Empty,
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK.f3EmptyMemsetGhostHook_eq]
  exact blk21TrapHook_memsetGhostHook emptyStdProg f3TrialRxProg (mmpl.base 21)
    (h2k_keepSub_covers_blk21 hMm L hL)

/-- `K`-narrowed `h2k_memsetGhostHookK mmpl` satisfies `Blk21TrapHook L` for every `L ∈ blk21`
    via its `.Exception` branch. -/
theorem h2k_memsetGhostHookK_blk21TrapHook {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L (h2k_memsetGhostHookK mmpl) :=
  fun L hL =>
    blk21TrapHook_of_exception_on_keepLr (h2k_keepSub_covers_blk21 hMm L hL) fun _ hkw =>
      exception_of_keepLr_false_of_noException h2k_memsetGhostHookK_keepLr_false_of_noException hkw

private def c3e5_isBlk20SafeInstr (off : Nat) (inst : Instr) : Bool :=
  match inst with
  | .ret rn => decide (rn = .lr)
  | .nop => decide (off + 4 < 396)
  | .bCond _ relOff =>
    decide (off + 4 < 396) && decide ((BitVec.ofNat 64 off + relOff).toNat < 396)
  | .cbz _ _ _ relOff =>
    decide (off + 4 < 396) && decide ((BitVec.ofNat 64 off + relOff).toNat < 396)
  | .tbz _ _ _ _ relOff =>
    decide (off + 4 < 396) && decide ((BitVec.ofNat 64 off + relOff).toNat < 396)
  | .addSubImm _ _ rd _ _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .addSubShift _ _ rd _ _ _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .logicalImm _ _ rd _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .bitfield _ _ rd _ _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .ldr _ _ _ rt addr =>
    decide (off + 4 < 396) && decide (rt ≠ .lr) && decide (addr.baseReg ≠ .lr)
  | .str _ _ addr =>
    decide (off + 4 < 396) && decide (addr.baseReg ≠ .lr)
  | .ldp _ _ rt1 rt2 addr =>
    decide (off + 4 < 396) && decide (rt1 ≠ .lr) && decide (rt2 ≠ .lr) &&
      decide (addr.baseReg ≠ .lr)
  | .stp _ _ _ addr =>
    decide (off + 4 < 396) && decide (addr.baseReg ≠ .lr)
  | _ => false

private theorem c3e5_memcpyWords_all_safe :
    ((List.range 99).all fun k =>
      match VerifiedLibraries.Musl.memcpySymWords[k]? with
      | some w =>
        match decode w with
        | some inst => c3e5_isBlk20SafeInstr (4 * k) inst
        | none => false
      | none => false) = true := by
  decide +kernel

private theorem c3e5_band_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> cases h
  exact ⟨rfl, rfl⟩

private theorem c3e5_lr_writeReg64 (s : State) {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
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

private def c3e5_Blk20StepOutcome (base : BitVec 64) (s s' : State) : Prop :=
  (∃ msg, s'.status = .Exception msg) ∨
  (s'.status = .Running ∧
   s'.readReg64 .lr = s.readReg64 .lr ∧
   (s'.pc = s.readReg64 .lr ∨ ∃ off' : Nat, off' < 396 ∧ s'.pc = base + BitVec.ofNat 64 off'))

private def c3e5_SameRunLrPc (s s1 : State) : Prop :=
  s1.status = s.status ∧ s1.readReg64 .lr = s.readReg64 .lr ∧ s1.pc = s.pc

private theorem c3e5_sameRunLrPc_refl (s : State) : c3e5_SameRunLrPc s s := ⟨rfl, rfl, rfl⟩

private theorem c3e5_sameRunLrPc_writeReg64 {s s1 : State} (h : c3e5_SameRunLrPc s s1)
    {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
    c3e5_SameRunLrPc s (s1.writeReg64 r v) :=
  ⟨h.1, (c3e5_lr_writeReg64 s1 hr v).trans h.2.1, h.2.2⟩

private theorem c3e5_sameRunLrPc_writeReg {s s1 : State} (h : c3e5_SameRunLrPc s s1)
    (w : Width) {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
    c3e5_SameRunLrPc s (s1.writeReg w r v) :=
  c3e5_sameRunLrPc_writeReg64 h hr _

private theorem c3e5_sameRunLrPc_setPState {s s1 : State} (h : c3e5_SameRunLrPc s s1) (ps : PState) :
    c3e5_SameRunLrPc s (s1.setPState ps) :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem c3e5_sameRunLrPc_optPState {s s1 : State} (h : c3e5_SameRunLrPc s s1)
    (optPs : Option PState) :
    c3e5_SameRunLrPc s (match optPs with | some ps => s1.setPState ps | none => s1) := by
  cases optPs with
  | none => exact h
  | some ps => exact c3e5_sameRunLrPc_setPState h ps

private theorem c3e5_sameRunLrPc_setMem {s s1 : State} (h : c3e5_SameRunLrPc s s1) (m : Memory) :
    c3e5_SameRunLrPc s (s1.setMem m) :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem c3e5_sameRunLrPc_addrWb {s s1 : State} (s0 : State) (h : c3e5_SameRunLrPc s s1)
    {addr : AddrMode} (hbr : addr.baseReg ≠ .lr) :
    c3e5_SameRunLrPc s (match (evalAddrMode s0 addr).2 with
      | some (base, newBase) => s1.writeReg64 base newBase
      | none => s1) := by
  cases addr <;> dsimp only [evalAddrMode, AddrMode.baseReg] at hbr ⊢
  · exact h
  · exact h
  · exact c3e5_sameRunLrPc_writeReg64 h hbr _
  · exact c3e5_sameRunLrPc_writeReg64 h hbr _
  · exact h

private theorem c3e5_outcome_of_advancePC {base : BitVec 64} {off : Nat} {s s1 : State}
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off)
    (hoff : off + 4 < 396)
    (h1 : c3e5_SameRunLrPc s s1) :
    c3e5_Blk20StepOutcome base s s1.advancePC := by
  refine Or.inr ⟨h1.1.trans hrun, h1.2.1, Or.inr ⟨off + 4, hoff, ?_⟩⟩
  change s1.pc + 4#64 = base + BitVec.ofNat 64 (off + 4)
  rw [h1.2.2, hpc, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem c3e5_outcome_of_branchRel {base : BitVec 64} {off : Nat} {relOff : BitVec 64} {s : State}
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off)
    (htgt : (BitVec.ofNat 64 off + relOff).toNat < 396) :
    c3e5_Blk20StepOutcome base s (s.setPC (s.pc + relOff)) := by
  refine Or.inr ⟨hrun, rfl, Or.inr ⟨(BitVec.ofNat 64 off + relOff).toNat, htgt, ?_⟩⟩
  change s.pc + relOff = base + BitVec.ofNat 64 (BitVec.ofNat 64 off + relOff).toNat
  rw [hpc, BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem c3e5_blk20_ite {base : BitVec 64} {s : State} {c : Prop} [inst : Decidable c]
    {t e : State} (ht : c3e5_Blk20StepOutcome base s t) (he : c3e5_Blk20StepOutcome base s e) :
    c3e5_Blk20StepOutcome base s (if c then t else e) :=
  match inst with
  | isTrue _ => ht
  | isFalse _ => he

private theorem c3e5_execInst_of_isBlk20SafeInstr
    {base : BitVec 64} {off : Nat} {inst : Instr} {s : State}
    (hsafe : c3e5_isBlk20SafeInstr off inst = true)
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off) :
    c3e5_Blk20StepOutcome base s (execInst inst s) := by
  cases inst <;> try (unfold c3e5_isBlk20SafeInstr at hsafe; contradiction)
  case ret rn =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    have hrn : rn = .lr := of_decide_eq_true hsafe
    subst hrn
    exact Or.inr ⟨hrun, rfl, Or.inl rfl⟩
  case nop =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    exact c3e5_outcome_of_advancePC hrun hpc (of_decide_eq_true hsafe) (c3e5_sameRunLrPc_refl s)
  case bCond cond relOff =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := c3e5_band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    change c3e5_Blk20StepOutcome base s
      (if Arm64.ConditionHolds cond s.pstate then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact c3e5_outcome_of_branchRel hrun hpc htgt
    · exact c3e5_outcome_of_advancePC hrun hpc hoff (c3e5_sameRunLrPc_refl s)
  case cbz w isNonZero rt relOff =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := c3e5_band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    let val := s.readReg w rt
    let c := if isNonZero then (val == 0#64) != true else val == 0#64
    change c3e5_Blk20StepOutcome base s (if c then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact c3e5_outcome_of_branchRel hrun hpc htgt
    · exact c3e5_outcome_of_advancePC hrun hpc hoff (c3e5_sameRunLrPc_refl s)
  case tbz w isNonZero rt bit relOff =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := c3e5_band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    change c3e5_Blk20StepOutcome base s
      (if (s.readReg64 rt).getLsbD bit == isNonZero then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact c3e5_outcome_of_branchRel hrun hpc htgt
    · exact c3e5_outcome_of_advancePC hrun hpc hoff (c3e5_sameRunLrPc_refl s)
  case addSubImm w op rd rn imm12 shift12 =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := c3e5_band_true hsafe
    exact c3e5_outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (c3e5_sameRunLrPc_optPState
        (c3e5_sameRunLrPc_writeReg (c3e5_sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case addSubShift w op rd rn rm shift amount =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := c3e5_band_true hsafe
    exact c3e5_outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (c3e5_sameRunLrPc_optPState
        (c3e5_sameRunLrPc_writeReg (c3e5_sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case logicalImm w op rd rn mask =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := c3e5_band_true hsafe
    exact c3e5_outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (c3e5_sameRunLrPc_optPState
        (c3e5_sameRunLrPc_writeReg (c3e5_sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case bitfield w op rd rn immr imms =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := c3e5_band_true hsafe
    exact c3e5_outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (c3e5_sameRunLrPc_writeReg (c3e5_sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _)
  case ldr w sz signed rt addr =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨h12, hbr0⟩ := c3e5_band_true hsafe
    obtain ⟨hoff0, hrt0⟩ := c3e5_band_true h12
    have hoff := of_decide_eq_true hoff0
    have hrt := of_decide_eq_true hrt0
    have hbr := of_decide_eq_true hbr0
    change c3e5_Blk20StepOutcome base s (execLdr w sz signed rt addr s)
    unfold execLdr
    split
    · exact Or.inl ⟨_, rfl⟩
    · dsimp only []
      split
      · exact Or.inl ⟨_, rfl⟩
      · exact c3e5_outcome_of_advancePC hrun hpc hoff
          (c3e5_sameRunLrPc_writeReg (c3e5_sameRunLrPc_addrWb s (c3e5_sameRunLrPc_refl s) hbr) w hrt _)
  case str sz rt addr =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := c3e5_band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hbr := of_decide_eq_true hbr0
    change c3e5_Blk20StepOutcome base s (execStr sz rt addr s)
    unfold execStr
    split
    · exact Or.inl ⟨_, rfl⟩
    · dsimp only []
      split
      · exact Or.inl ⟨_, rfl⟩
      · exact c3e5_outcome_of_advancePC hrun hpc hoff
          (c3e5_sameRunLrPc_addrWb s (c3e5_sameRunLrPc_setMem (c3e5_sameRunLrPc_refl s) _) hbr)
  case ldp w signed rt1 rt2 addr =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨h123, hbr0⟩ := c3e5_band_true hsafe
    obtain ⟨h12, hrt20⟩ := c3e5_band_true h123
    obtain ⟨hoff0, hrt10⟩ := c3e5_band_true h12
    have hoff := of_decide_eq_true hoff0
    have hrt1 := of_decide_eq_true hrt10
    have hrt2 := of_decide_eq_true hrt20
    have hbr := of_decide_eq_true hbr0
    change c3e5_Blk20StepOutcome base s (execLdp w signed rt1 rt2 addr s)
    unfold execLdp
    exact c3e5_blk20_ite (Or.inl ⟨_, rfl⟩)
      (c3e5_blk20_ite (Or.inl ⟨_, rfl⟩)
        (c3e5_outcome_of_advancePC hrun hpc hoff
          (c3e5_sameRunLrPc_writeReg
            (c3e5_sameRunLrPc_writeReg (c3e5_sameRunLrPc_addrWb s (c3e5_sameRunLrPc_refl s) hbr) _ hrt1 _)
            _ hrt2 _)))
  case stp w rt1 rt2 addr =>
    unfold c3e5_isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := c3e5_band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hbr := of_decide_eq_true hbr0
    change c3e5_Blk20StepOutcome base s (execStp w rt1 rt2 addr s)
    unfold execStp
    exact c3e5_blk20_ite (Or.inl ⟨_, rfl⟩)
      (c3e5_blk20_ite (Or.inl ⟨_, rfl⟩)
        (c3e5_outcome_of_advancePC hrun hpc hoff
          (c3e5_sameRunLrPc_addrWb s (c3e5_sameRunLrPc_setMem (c3e5_sameRunLrPc_refl s) _) hbr)))

private theorem c3e5_codeLoaded_of_strip_blk20 {mmpl : MultiPlacement} {m : Memory}
    (hcl : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded
      (stripExecOutside (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.keepMemcpyBlk20 mmpl) m)) :
    (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m := by
  rw [Arm64.Program.codeLoaded_iff] at hcl ⊢
  refine ⟨hcl.1, hcl.2.1, fun i hi => ?_⟩
  have hlen : (mallocngBlockProg mmpl 20 Syscall.standard).code.length = 396 := by
    rw [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap.mallocngBlockProg20_code_length]
  have hk : LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.keepMemcpyBlk20 mmpl
      ((mallocngBlockProg mmpl 20 Syscall.standard).base + BitVec.ofNat 64 i) = true :=
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.keepCoversBlk20_keepMemcpyBlk20
      mmpl i (hlen ▸ hi)
  have hcell : (stripExecOutside
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.keepMemcpyBlk20 mmpl) m).cells
      ((mallocngBlockProg mmpl 20 Syscall.standard).base + BitVec.ofNat 64 i) =
      m.cells ((mallocngBlockProg mmpl 20 Syscall.standard).base + BitVec.ofNat 64 i) := by
    simp only [stripExecOutside, hk]
    rcases m.cells ((mallocngBlockProg mmpl 20 Syscall.standard).base + BitVec.ofNat 64 i) with
      _ | ⟨_ | p, b⟩ <;> rfl
  have hi_s := hcl.2.2 i hi
  unfold Memory.read8 Memory.perm Memory.isLazyFree at hi_s ⊢
  rwa [hcell] at hi_s

private theorem c3e5_visitedIn_blk20_preserves_lr {mmpl : MultiPlacement} {z sf : State}
    (hvis : LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric.h2fsgen_StepsVisitedIn
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.keepMemcpyBlk20 mmpl)
      emptyStdProg z sf)
    (hcl : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded z.mem)
    (hrun_sf : sf.status = .Running) :
    sf.readReg64 .lr = z.readReg64 .lr := by
  induction hvis with
  | refl _ => rfl
  | @step s1 s2 s3 hd h1 h2 ih =>
    have hcl2 := h1.codeLoaded hcl
    have hrun2 : s2.status = .Running := by
      by_contra hnr
      have heq := ProofLib.Variant.Steps.eq_of_not_running h2.toSteps hnr
      exact hnr (heq ▸ hrun_sf)
    cases h1 with
    | halt_unmapped _ _ _ => cases hrun2
    | extern _ heg _ _ => cases heg
    | extern_fault _ heg _ => cases heg
    | @exec inst hrun1 hfm =>
      have hoff_lt : (s1.pc - mmpl.base 20).toNat < 396 := of_decide_eq_true hd
      let off := (s1.pc - mmpl.base 20).toNat
      have hpc_eq : s1.pc = mmpl.base 20 + BitVec.ofNat 64 off := by
        dsimp only [off]
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm (mmpl.base 20),
          BitVec.sub_add_cancel]
      have hfm0 := hfm
      unfold Program.fetchMem at hfm0
      have heg0 : emptyStdProg.externAt? s1.pc = none := rfl
      simp only [heg0, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm0
      split at hfm0
      · contradiction
      rename_i hal_neg
      have hal : s1.pc.toNat % 4 = 0 := Classical.not_not.mp hal_neg
      have hbase_al : (mmpl.base 20).toNat % 4 = 0 := hcl.aligned
      have hnowrap : (mmpl.base 20).toNat + 396 ≤ 2 ^ 64 := by
        have hnw := hcl.no_wrap
        rwa [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap.mallocngBlockProg20_code_length mmpl] at hnw
      have hpc_nat : s1.pc.toNat = (mmpl.base 20).toNat + off := by
        rw [hpc_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      let k := off / 4
      have hoff_k : off = 4 * k := by omega
      have hk : k < 99 := by omega
      have hk_len : k < VerifiedLibraries.Musl.memcpySymWords.length := by
        have hl : VerifiedLibraries.Musl.memcpySymWords.length = 99 := by decide
        omega
      have hall_k := List.all_eq_true.mp c3e5_memcpyWords_all_safe k (List.mem_range.mpr hk)
      rw [List.getElem?_eq_getElem hk_len] at hall_k
      dsimp only [] at hall_k
      cases hdec : decode VerifiedLibraries.Musl.memcpySymWords[k] with
      | none => rw [hdec] at hall_k; contradiction
      | some inst_k =>
        rw [hdec] at hall_k
        dsimp only [] at hall_k
        let P_sub := mallocngBlockProg mmpl 20 Syscall.standard
        have hrw :=
          (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode.mallocngBlockProg20_hasWords
            mmpl Syscall.standard).2.1 k hk_len
        change P_sub.readWordOff ((mmpl.base 20 - mmpl.base 20).toNat + 4 * k) =
          some VerifiedLibraries.Musl.memcpySymWords[k] at hrw
        rw [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, ← hoff_k] at hrw
        have hext_sub : P_sub.externAt? s1.pc = none :=
          LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode.mallocngBlockProg20_externAt_none
            mmpl Syscall.standard s1.pc
        have hfetch_sub : P_sub.fetch s1.pc = some inst_k := by
          unfold Program.fetch
          have hbase_sub : (s1.pc - P_sub.base).toNat = off := rfl
          rw [hext_sub, hbase_sub, hrw]; exact hdec
        have hfm_sub : P_sub.fetchMem s1.mem s1.pc = some inst_k :=
          P_sub.fetchMem_of_fetch hcl hfetch_sub
        have hfm_eq : emptyStdProg.fetchMem s1.mem s1.pc = P_sub.fetchMem s1.mem s1.pc :=
          ProofLib.Variant.fetchMem_eq_of_externAt_eq (heg0.trans hext_sub.symm)
        rw [hfm_eq, hfm_sub] at hfm
        injection hfm with hinst_eq
        subst inst_k
        have hsafe : c3e5_isBlk20SafeInstr off inst = true := hoff_k ▸ hall_k
        have hev : emptyStdProg.evalInst inst s1 = execInst inst s1 := by
          cases inst <;> first | rfl | cases hsafe
        rw [hev] at h2 hcl2 hrun2 ih
        rcases c3e5_execInst_of_isBlk20SafeInstr hsafe hrun1 hpc_eq with ⟨msg, hex⟩ | ⟨_, hlr_eq, _⟩
        · rw [hex] at hrun2; contradiction
        · exact (ih hcl2 hrun_sf).trans hlr_eq

private theorem c3e5_f3EmptyMemcpyGhostHookNarrow_blk21TrapHook
    (mmpl : MultiPlacement) (L : BitVec 64) :
    Blk21TrapHook L
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow mmpl) := by
  classical
  intro w hrun hlr
  rw [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1.narrowMemcpyGhostHook
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.memcpyGhostHook
    LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.linkedCallHook
  by_cases hPre :
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.ActiveRealPre
        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode.masterMemcpySpec w
  · simp only [hPre, ↓reduceDIte]
    by_cases hReal :
        ActiveRealRun
          (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.keepMemcpyBlk20 mmpl)
          (Program.ofSvc Syscall.standard) (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20) w
    · simp only [hReal, ↓reduceDIte]
      obtain ⟨_, hsp, x, R, hpre⟩ := hPre
      obtain ⟨sf, huntil, hstop, hout, _, _, _, hvis⟩ :=
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric.h2fsgen_real_subroutine_run_visitedIn_of_stripS
          (P1 := emptyStdProg) rfl
          (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn.mallocngBlockProg20_svc_eq mmpl)
          (fun _ _ => rfl)
          (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode.mallocngBlockProg20_externAt_none mmpl Syscall.standard)
          (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode.subroutine_ok_masterMemcpy_of_hasWords
            (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode.mallocngBlockProg20_externAt_none mmpl Syscall.standard)
            (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode.mallocngBlockProg20_hasWords mmpl Syscall.standard))
          (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.specStripSInvariant_masterMemcpy _)
          LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.specPreservesFsTrace_masterMemcpy
          LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.masterMemcpy_pre_setPC
          LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.masterMemcpy_outcome_setPC
          hrun hsp hpre hReal.1 hReal.2.1 hReal.2.2.1
      have hchoose := Classical.choose_spec hReal.2.2.2
      have hdet : Classical.choose hReal.2.2.2 = sf :=
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric.h2fsgen_stepsUntil_det
          hchoose.1 hchoose.2.1 huntil hstop
      rw [hdet]
      rcases hout with ⟨⟨hpc_sf, _, hrun_sf⟩, _, _⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
      · have hcl_set : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded
            (w.setPC (mmpl.base 20)).mem := by
          have hm : (w.setPC (mmpl.base 20)).mem = w.mem := by cases w; rfl
          rw [hm]; exact c3e5_codeLoaded_of_strip_blk20 hReal.2.2.1
        have hlr_set : (w.setPC (mmpl.base 20)).readReg64 .lr = L := by
          have hl0 : (w.setPC (mmpl.base 20)).readReg64 .lr = w.readReg64 .lr := by cases w; rfl
          exact hl0.trans hlr
        have hlr_sf : sf.readReg64 .lr = L :=
          (c3e5_visitedIn_blk20_preserves_lr hvis hcl_set hrun_sf).trans hlr_set
        exact Or.inr ⟨hrun_sf, hpc_sf.trans hlr, hlr_sf⟩
      · simp [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode.masterMemcpySpec] at hp
      · simp [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode.masterMemcpySpec] at he
      · simp [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode.masterMemcpySpec] at ho
    · simp only [hReal, ↓reduceDIte,
        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost.keepFsTrace_hookMemcpy_eq]
      exact LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet.blk21TrapHook_hookMemcpy
        L w hrun hlr
  · simp only [hPre, ↓reduceDIte]
    exact Or.inl ⟨"ghost-hook precondition violated", rfl⟩

/-- **Concrete `(A2)` mixed-pass `Blk21TrapHook` theorem for all 9 non-shim F3 ghosts in
    `h2k_ghFixedK`:**
    Every non-shim ghost hook `f` in `cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none)`
    satisfies `∀ L, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f`. -/
theorem h2k_ghFixedK_blk21TrapHook [LibsignalPlacement]
    (mpl : MultiPlacement) {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {sym : String} {f : State → State}
    (hext : cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f)
    (hnoShim : sym ≠ lsRustNoAllocShimSymCli) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f := by
  intro L hL
  by_cases hms : sym = CryptoVerification.SignalSession.lsMemsetSym
  · subst hms
    have heq : cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none)
        CryptoVerification.SignalSession.lsMemsetSym =
        some (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow mmpl) :=
      rfl
    rw [heq] at hext; injection hext with hfeq; subst hfeq
    rw [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow_eq_narrow]
    exact blk21TrapHook_memsetGhostHook emptyStdProg
      (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21) hL
  · by_cases hmc : sym = CryptoVerification.SignalSession.lsMemcpySym
    · subst hmc
      have heq : cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none)
          CryptoVerification.SignalSession.lsMemcpySym =
          some (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow mmpl) :=
        rfl
      rw [heq] at hext; injection hext with hfeq; subst hfeq
      exact c3e5_f3EmptyMemcpyGhostHookNarrow_blk21TrapHook mmpl L
    · exact blk21TrapHook_of_exception_on_keepLr (h2k_keepSub_covers_blk21 hMm L hL) fun _ hkw =>
        exception_of_keepLr_false_of_noException
          (fun hnoex => h2k_keepSubLr_false_of_noException mpl mmpl hext hnoShim hnoex hms hmc) hkw

/-- **`W`-independent narrow (`keepMemsetBlk21 mmpl`) `memset` ghost hook (`h2k_memsetGhostHookNarrow`):**
    Uses `P_real := hole2_emptyProg` (so it can be fixed outside `∀ W` in `Block617TransferFixedHyp`),
    satisfies **plain** `HookOk` (`h2k_memsetGhostHookNarrow_master_ok`, zero `lr` precondition on
    callers even inside `hole2_keepSub`), and discharges `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false`
    via the `(A1)`+`(A2)` closed-trap lemma (`h2k_memsetGhostHookNarrow_stub_replayOn_of_trap_ret` +
    `h2k_cliGhostExterns_ghFixedK_blk21_ext` / `h2k_ghFixedK_blk21_ext_trap`).
    *Route note (`rev_c6` F1):* Use this hook + `h2k_memsetGhostHookNarrow_stub_replayOn_of_trap_ret` for
    Option `(i)` / Variant A (as opposed to `h2k_memsetGhostHookK` for Option `(ii)` / K route; plain
    `h2k_memsetGhostHook` is unusable for Option `(i)`). -/
@[expose] noncomputable def h2k_memsetGhostHookNarrow (mmpl : MultiPlacement) : State → State :=
  f3LinkedCallHook (keepMemsetBlk21 mmpl) hole2_emptyProg
    (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21)
    (fun _ _ => masterMemsetSpec) hookMemset

theorem h2k_memsetGhostHookNarrow_master_ok (mmpl : MultiPlacement) :
    HookOk (h2k_memsetGhostHookNarrow mmpl) masterMemsetSpec :=
  f3EmptyMemsetGhostHook_master_ok (mallocngBlockProg21_svc_eq mmpl)
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

theorem h2k_memsetGhostHookNarrow_sessionMemsetRegion_ok (mmpl : MultiPlacement) :
    HookOk (h2k_memsetGhostHookNarrow mmpl) sessionMemsetRegionSpec :=
  f3EmptyMemsetGhostHook_sessionMemsetRegion_ok (mallocngBlockProg21_svc_eq mmpl)
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

theorem h2k_memsetGhostHookNarrow_sessionMemsetRegionBudget_ok (mmpl : MultiPlacement) :
    HookOk (h2k_memsetGhostHookNarrow mmpl) sessionMemsetRegionBudgetSpec :=
  f3EmptyMemsetGhostHook_sessionMemsetRegionBudget_ok (mallocngBlockProg21_svc_eq mmpl)
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

theorem h2k_memsetGhostHookNarrow_blk21TrapHook (mmpl : MultiPlacement) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L (h2k_memsetGhostHookNarrow mmpl) := by
  intro L hL
  change Blk21TrapHook L
    (f3EmptyMemsetGhostHook (keepMemsetBlk21 mmpl)
      (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21))
  rw [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK.f3EmptyMemsetGhostHook_eq]
  exact blk21TrapHook_memsetGhostHook emptyStdProg
    (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21) hL

/-- **`W`-polymorphic `(A1)` + `(A2)` trap-discharged behind-stub `On` replay for
    `h2k_memsetGhostHookNarrow`:**
    Combines `W`-independence (`P_real = hole2_emptyProg`, bridged by
    `h2sl_steps_realW_of_visitedIn_keepSub`), guarded `StubReachesTargetOn (F3CodeInv mpl mmpl)`,
    and `(A1)` + `(A2)` closed-trap discharge of `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false`
    (supporting subroutine `Returned` outcomes when `keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false`,
    such as `sm.lr` at the Block-617 entry!). -/
theorem h2k_memsetGhostHookNarrow_stub_replayOn_of_trap_ret
    {P_ghost : Program} {mpl mmpl : MultiPlacement} {stubPc : BitVec 64}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hreal_stub_none : (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc =
      none)
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc (mmpl.base 21))
    {sf : State}
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    let f_ms := h2k_memsetGhostHookNarrow mmpl
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubPc = none ∧
    ∀ u : State,
      Steps P_ghost (f_ms u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f_ms u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f_ms u).mem →
      ExecFrozen u.mem →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f_ms u) ∧
        ExecFrozen (f_ms u).mem ∧
        F3CodeInv mpl mmpl (f_ms u).mem ∧
        (f_ms u).fs = u.fs := by
  have h21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  refine ⟨hreal_stub_none, fun u hrest hpc hrun hnoex hkf hfr hInv => ?_⟩
  have hcl21 : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded u.mem :=
    hInv.mngBlockCodeLoaded 21 h21 (fun _ => none) (fun _ => none) Syscall.standard
  have hlr_false : keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
    blk21_lr_trap_after_hook_ret
      (h2k_memsetGhostHookNarrow_blk21TrapHook mmpl)
      hblk21_ext
      (hcl21.of_keepsFrozen hkf)
      hrest hrun hrun_sf' hnoex_sf hnhalt_sf
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
    f3LinkedCallHook_empty_visitedIn
      (mallocngBlockProg21_svc_eq mmpl)
      (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
      (subroutine_ok_masterMemset_of_hasWords
        (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
        (mallocngBlockProg21_hasWords mmpl Syscall.standard))
      (specStripSInvariant_masterMemset (keepMemsetBlk21 mmpl))
      specPreservesFsTrace_masterMemset masterMemset_pre_setPC masterMemset_outcome_setPC
      hrun hnoex hfr hlr_false
      (codeLoaded_stripExecOutside_blk21 (keepCoversBlk21_keepMemsetBlk21 mmpl) hcl21)
  have hBody :=
    h2sl_steps_realW_of_visitedIn_keepSub hLs mmpl W
      (stepsVisitedIn_mono (h2k_keepSub_covers_blk21 hMm) hvis)
  have hSteps := (hStub u hpc hrun hfr hInv).trans hBody
  exact ⟨hSteps, hfr_sf, hInv.of_keepsFrozen hSteps.keepsFrozen, hfs_sf⟩

/-! ## 6. Closed Ghost-Side `hblk21_ext` for CLI Block `617` (`rev_c6` F3) -/

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
  dsimp only [cliProgExtPlacedAt, MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
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
    rw [Obj.Interned.getD_of_lt hlt]; exact List.getElem_mem hlt
  rw [(f3CliElf_libsignal_inElf_unique hpl hin).2.1 _ hmem, ls_toMultiPlacedLib_eq]
  change lsInternedMultiLib.toMultiPlacedLib.resolve
    (ElfCodeMatchesPlaced.f3LsLayout.toMultiPlacement lsInternedMultiLib.names) _ = _
  rw [Obj.Interned.toMultiPlacement_resolve_eq ls_names_nodup ls_idsOk ls_blockSymsMatch_ok,
    Obj.Interned.idxOf_getD ls_names_nodup hlt]
  rfl

private theorem keepMemsetBlk21_eq_f3 {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    keepMemsetBlk21 mmpl = keepMemsetBlk21 f3MallocngMpl := by
  funext a; unfold keepMemsetBlk21
  have h21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  rw [(f3CliElf_mallocng_linkedAt_unique hMm).1 21 h21]

private noncomputable def h2k_shimDisjointBlk21B : Bool :=
  lsSharedExterns.any fun idx =>
    (lsInternedMultiLib.names.getD idx "" == lsRustNoAllocShimSymCli) &&
    !(keepMemsetBlk21 f3MallocngMpl (f3LsSymAddrs.getD idx 0#64))

set_option maxRecDepth 4000000 in
private theorem h2k_shimDisjointBlk21_ok : h2k_shimDisjointBlk21B = true := by rfl_kernel

/-- The `lsRustNoAllocShimSymCli` stub PC lies outside `keepMemsetBlk21 mmpl` (`rev_c6` F3). -/
theorem h2k_shimStub_not_in_blk21 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    keepMemsetBlk21 mmpl (libsignalSessionLib.resolve mpl lsRustNoAllocShimSymCli) = false := by
  obtain ⟨idx, hidx, hpred⟩ := List.any_eq_true.mp h2k_shimDisjointBlk21_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  rw [keepMemsetBlk21_eq_f3 hMm, ← hpred.1, resolve_idx_of_linkedAt hLs hidx]
  cases hb : keepMemsetBlk21 f3MallocngMpl (f3LsSymAddrs.getD idx 0#64)
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
                · by_cases h9 : sym == CryptoVerification.SignalSession.lsMemsetSym
                  · cases hms : g.memset <;>
                      simp only [h6, h7, h8, h9, hms, Bool.false_eq_true, ↓reduceIte] at hext ⊢
                    · exact Or.inr hext
                    · exact Or.inl ⟨h5, hext⟩
                  · by_cases h10 : sym == CryptoVerification.SignalSession.lsMemcpySym
                    · cases hmc : g.memcpy <;>
                        simp only [h6, h7, h8, h9, h10, hmc, Bool.false_eq_true, ↓reduceIte] at hext ⊢
                      · exact Or.inr hext
                      · exact Or.inl ⟨h5, hext⟩
                    · simp only [h6, h7, h8, h9, h10, Bool.false_eq_true, ↓reduceIte] at hext
                      exact Or.inr hext

/-- **Compositional ghost-side `hblk21_ext` (`rev_c6` F3):** combines `h2k_ghFixedK_blk21TrapHook`
    (7 K ghosts), `h2k_memsetGhostHookNarrow_blk21TrapHook` (`memset`), `h2k_shimStub_not_in_blk21`
    (`shim`), and `h2sl_realW_noExtern_keepSub` on any base map `baseExt ⊆ cliExternsPlaced mmpl`. -/
theorem h2k_cliGhostExterns_ghFixedK_blk21_ext [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (baseExt : CliHooks → String → Option (State → State))
    (hbase_sub : ∀ W sym, baseExt W sym = none ∨ baseExt W sym = cliExternsPlaced mmpl W sym)
    (W : CliHooks) :
    let P_ghost := cliProgExtPlacedAt mpl
      (fun W' sym =>
        if sym == "memset" then some (h2k_memsetGhostHookNarrow mmpl)
        else cliGhostExterns (h2k_ghFixedK mpl mmpl) (baseExt W') sym) 617 W
    ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f := by
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
      by_cases hms : sym == "memset"
      · simp only [hms, ↓reduceIte, Option.some.injEq] at hsym_ite; subst hsym_ite
        exact h2k_memsetGhostHookNarrow_blk21TrapHook mmpl
      · simp only [hms, Bool.false_eq_true, ↓reduceIte] at hsym_ite
        rcases cliGhostExterns_some_cases (h2k_ghFixedK mpl mmpl) (baseExt W) hsym_ite with
          rfl | ⟨hne, hgh⟩ | hbase
        · exfalso; have hns := h2k_shimStub_not_in_blk21 hLs hMm
          rw [hres, hpc] at hns; exact Bool.noConfusion hns
        · exact h2k_ghFixedK_blk21TrapHook mpl hMm hgh hne
        · exfalso
          rcases hbase_sub W sym with hnone | heq_real
          · rw [hnone] at hbase; cases hbase
          · rw [heq_real] at hbase
            have hreal_none :=
              h2sl_realW_noExtern_keepSub hLs mmpl W pc (h2k_keepSub_covers_blk21 hMm pc hpc)
            rw [externAt?_cliProgExtPlacedAt_any] at hreal_none
            have hcell := findSome?_eq_none_imp hreal_none hsym_mem
            rw [hres_eq, hbase] at hcell; cases hcell

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset
