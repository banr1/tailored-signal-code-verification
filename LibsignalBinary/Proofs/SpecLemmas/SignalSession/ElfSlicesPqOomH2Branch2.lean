/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Proofs.Common.StringClonePlaced
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2CodeLoadedInv
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopRealloc
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import ProofLib
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopDealloc
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReads

/-!
# Stub Target Resolution and Per-Hook Branch-2 Replay (`ElfSlicesPqOomH2Branch2`)

**Checked by Lean.**

Provides the 0-new-invariant `Ghost617Transfer.StubReachesTargetOn (F3CodeInv mpl mmpl)` witnesses
(`h2b2_stub_*`), raw ELF load bridge (`h2b2_unpatched_load`), stub-PC resolution identities
(`libsignalSessionLib.resolve mpl sym = mpl.ρ sym`), ELF `.symtab` target-VA identities
(`Obj.lookupUnique sym cliElfImage.symbols = some (hole2_targets mpl).<hook>`), real `externAt? = none`
on active ghost symbols, and full branch-2 replay for `lsRustNoAllocShimSymCli` (`h2b2_shim_branch2`):

1. **`h2b2_unpatched_load`**: public derivation of `∃ inputs sRaw, cliElfImage.loadState inputs = .ok sRaw ∧ sRaw.mem.KeepsFrozen m`
   from `hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl` and `hInv : F3CodeInv mpl mmpl m` (`0` new `InvS` conjuncts).
2. **Stub-PC Resolution (`SR3` check `(i)`)**: `libsignalSessionLib.resolve mpl sym = mpl.ρ sym` on all `7`
   symbols in `cliDehookedSymsPlaced` (`lsRustNoAllocShimSymCli`, `lsRustAllocSymCli`, `lsRustDeallocSymCli`,
   `lsRustReallocSymCli`, `lsRustAllocZeroedSymCli`, `lsReadFileSym`, `lsReadStdinSym`), plus
   `libsignalSessionLib.resolve mpl lsStringClonePlacedSym = (hole2_targets mpl).stringClone` (`mpl.base 623`)
   and `h2b2_strCloneSym_not_mem_ext617` (`lsStringCloneSym ∉ (libsignalSessionLib.blockLib 617).text.externs`).
3. **Target-VA Equalities (`SR3` check `(ii)`)**: `Obj.lookupUnique sym cliElfImage.symbols = some ...`
   for the `4` `rdl_shim.S` allocator thunks (`f3StubAddrs.{alloc,dealloc,realloc}`, `f3StubAzAddr`),
   `(hole2_targets mpl).{readFile,readStdin}`, and `f3NoShimV2Addr` (`0x469640#64`) for `lsRustNoAllocShimSymCli`.
4. **`StubReachesTargetOn (F3CodeInv mpl mmpl)` (`SR3` check `(iii)`)**: `h2b2_stub_alloc`, `h2b2_stub_dealloc`,
   `h2b2_stub_realloc`, `h2b2_stub_allocZeroed`, `h2b2_stub_readFile`, `h2b2_stub_readStdin`,
   `h2b2_stub_stringClone`, `h2b2_stub_stringClone_target`, and `h2b2_stub_shim`, plus `h2b2_shim_steps`
   / `h2b2_shim_branch2` and `cliGhostExterns` / `GhostSymActive` bridges.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Branch2

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open VerifiedLibraries (mallocngLib)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks cliDehookedSymsPlaced cliElfBytes cliElfImage cliElf_staticOk cliExternsPlaced
   libsignalSessionLib lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli
   lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks IsFsC cliGhostExterns cliGhostExterns_memcpy_some cliGhostExterns_memset_some)
open CryptoVerification.SignalSession.Placed (DirectOrBranchStub)
open LibsignalBinary.Heap (rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.Fine
  (f3NoShimV2Addr f3RdlAddrs f3RdlAzAddr f3StubAddrs f3StubAzAddr fineCostModel
   fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.Common.StringClonePlaced
  (lsStringClonePlacedSym ls_resolve_stringClone)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen StubReachesTarget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (ActiveF3ReadFileRun F3ReadFileFixedCallGuard readFileAnySpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
  (ActiveReadStdinLinkedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3LinkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt loadState_patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (GhostSymActive StubReachesTargetOn stubReachesTargetOn_of_directOrBranchStub)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (cliDehookedSymsPlaced_eq_entries f3DehookedEntries lsInternedMultiLib lsSharedExterns
   ls_block617_externs_eq ls_idsOk ls_names_nodup ls_sharedExterns_lt ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3TrialElfSymChars f3TrialElfSyms_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv cliElf_tokenCellsPlacedAt_of_linkedAt keepsFrozen_cliTokenPatchPlacedAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3Trial_rustStdThunkCode f3Trial_seg5ShimBundle f3Trial_stubAz_hasInstrs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2CodeLoadedInv
  (h2cl_f3CodeInv_rxProg_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc
  (h2fsalloc_alloc_firstStop_keepSub h2fsalloc_allocZeroed_firstStop_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopDealloc
  (h2fsdealloc_firstStop_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReads
  (h2fsreads_readFile_activeRealRun_keepSub h2fsreads_readFile_firstStop_keepSub
   h2fsreads_readStdin_activeRealRun_keepSub h2fsreads_readStdin_firstStop_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopRealloc
  (h2fsrealloc_activeRealRun h2fsrealloc_firstStop_of_keep h2fsrealloc_keepSub_mallocng
   h2fsrealloc_spec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_fds_of_noException h2k_ghFixedK h2k_keepLr_false_of_noException h2k_keepSetForSym
   h2k_keepSubLr_false_of_noException h2k_readFileAnySpecK h2k_readFileFixedGhostHookFineK
   h2k_readFileFixedGhostHookFineSubK h2k_readStdinGhostHookFineK
   h2k_readStdinGhostHookFineSubK h2k_readStdinSpecK h2k_withKeepLrAndFds h2k_withKeepLrFalse)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2
  (h2sl_emptyProg_externAt h2sl_emptyProg_svc h2sl_realW_dehooked_witness
   h2sl_realW_noExtern_keepSub h2sl_stepsUntil_emptyProg_to_realW_of_allProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_hookStack hole2_keep hole2_keepSub hole2_targets)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (wp4MemcpyRealAddr wp4MemsetRealAddr)

/-! ## Unpatched Raw ELF Load Bridge -/

/-- From `hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl` and `hInv : F3CodeInv mpl mmpl m`,
    recover an unpatched `cliElfImage.loadState inputs = .ok sRaw` whose frozen bytes/permissions
    are preserved in `m` (`sRaw.mem.KeepsFrozen m`). -/
theorem h2b2_unpatched_load {mpl mmpl : MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    ∃ (inputs : ProcessInputs) (sRaw : State),
      cliElfImage.loadState inputs = .ok sRaw ∧ sRaw.mem.KeepsFrozen m := by
  obtain ⟨inputs, sLoad, hload, hkfLoad⟩ := hInv.fromLoad
  have htok := cliElf_tokenCellsPlacedAt_of_linkedAt hLs
  have hmap := loadState_patchElfTokensPlacedAt cliElf_staticOk htok inputs
  rw [hmap] at hload
  cases hraw : cliElfImage.loadState inputs with
  | error _ =>
    rw [hraw] at hload
    cases hload
  | ok sRaw =>
    rw [hraw] at hload
    simp only [Except.map, Except.ok.injEq] at hload
    have hkf0 : sRaw.mem.KeepsFrozen sLoad.mem := by
      rw [← hload]
      exact keepsFrozen_cliTokenPatchPlacedAt cliElf_staticOk htok hraw
    exact ⟨inputs, sRaw, hraw, hkf0.trans hkfLoad⟩

/-! ## Dehooked Symbol Resolution and `.symtab` Target-VA Table -/

/-- Expected `(symbol, targetVa)` pairs for the `9` symbols in `cliDehookedSymsPlaced`:
    `shim` (`f3NoShimV2Addr = 0x469640#64`), the `4` `rdl_shim.S` allocator thunk entries
    (`f3StubAddrs.{alloc,dealloc,realloc}`, `f3StubAzAddr`), the `2` IO entries
    (`readFile` at `0x4691b4#64`, `readStdin` at `0x469000#64`), and
    `memcpy` (`wp4MemcpyRealAddr`), `memset` (`wp4MemsetRealAddr`). -/
def h2b2_dehookedTargetPairs : List (String × BitVec 64) :=
  [ (lsRustNoAllocShimSymCli, f3NoShimV2Addr),
    (lsRustAllocSymCli, f3StubAddrs.alloc),
    (lsRustDeallocSymCli, f3StubAddrs.dealloc),
    (lsRustReallocSymCli, f3StubAddrs.realloc),
    (lsRustAllocZeroedSymCli, f3StubAzAddr),
    (lsReadFileSym, 0x4691b4#64),
    (lsReadStdinSym, 0x469000#64),
    ("memcpy", wp4MemcpyRealAddr),
    ("memset", wp4MemsetRealAddr) ]

private theorem h2b2_f3DehookedEntries_pairs_eq :
    (f3DehookedEntries.map fun e => (String.ofList e.2.1, e.2.2.2)) = h2b2_dehookedTargetPairs := by
  rfl_kernel

private noncomputable def h2b2_checkDehookedMetaB : Bool :=
  Obj.Interned.buildEncSymTable f3TrialElfSymChars fun enc =>
    f3DehookedEntries.all fun (idx, cs, _, targetVa) =>
      Nat.blt idx lsInternedMultiLib.names.length &&
      (lsInternedMultiLib.names.getD idx "" == String.ofList cs) &&
      (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none) &&
      (Obj.Interned.withEncodeCharKey cs fun key =>
        ProofLib.ObjectLoad.lookupUniqueEnc key enc == some targetVa)

set_option maxRecDepth 4000000 in
private theorem h2b2_checkDehookedMeta_ok : h2b2_checkDehookedMetaB = true := by
  rfl_kernel

private theorem h2b2_lookupBlockSym_none_of_idx {idx : Nat} {s : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (heq : lsInternedMultiLib.names.getD idx "" = s)
    (hid : Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks = none) :
    Obj.lookupBlockSym s libsignalSessionLib.blocks = none := by
  rw [← heq, ls_toMultiPlacedLib_eq,
    Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hlt]
  exact hid

private theorem h2b2_dehooked_pair_facts {mpl : MultiPlacement} {sym : String} {tgt : BitVec 64}
    (hmem : (sym, tgt) ∈ h2b2_dehookedTargetPairs) :
    sym ∈ cliDehookedSymsPlaced ∧
    libsignalSessionLib.resolve mpl sym = mpl.ρ sym ∧
    Obj.lookupUnique sym cliElfImage.symbols = some tgt := by
  rw [← h2b2_f3DehookedEntries_pairs_eq, List.mem_map] at hmem
  obtain ⟨⟨idx, cs, stubVa, targetVa⟩, hmem_e, heq_pair⟩ := hmem
  dsimp only at heq_pair
  injection heq_pair with hsym_eq htgt_eq
  subst hsym_eq htgt_eq
  have hchk := h2b2_checkDehookedMeta_ok
  unfold h2b2_checkDehookedMetaB at hchk
  rw [Obj.Interned.buildEncSymTable_eq] at hchk
  have he := List.all_eq_true.mp hchk (idx, cs, stubVa, targetVa) hmem_e
  simp only [Obj.Interned.withEncodeCharKey_eq, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at he
  obtain ⟨⟨⟨hlt, hname⟩, hid⟩, hlu_enc⟩ := he
  have hmem_dehook : String.ofList cs ∈ cliDehookedSymsPlaced := by
    rw [cliDehookedSymsPlaced_eq_entries, List.mem_map]
    exact ⟨(idx, cs, stubVa, targetVa), hmem_e, rfl⟩
  have hnone := h2b2_lookupBlockSym_none_of_idx hlt hname hid
  have hres : libsignalSessionLib.resolve mpl (String.ofList cs) = mpl.ρ (String.ofList cs) := by
    unfold MultiPlacedLib.resolve
    rw [hnone]
  have hlu : Obj.lookupUnique (String.ofList cs) cliElfImage.symbols = some targetVa := by
    change Obj.lookupUnique (String.ofList cs)
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.f3TrialElf.symbols =
      some targetVa
    rw [ProofLib.ObjectLoad.lookupUnique_eq_lookupUniqueEnc f3TrialElfSyms_eq rfl rfl]
    exact hlu_enc
  exact ⟨hmem_dehook, hres, hlu⟩

/-- Every `sym ∈ cliDehookedSymsPlaced` is an external symbol (`lookupBlockSym = none`), so
    `libsignalSessionLib.resolve mpl sym = mpl.ρ sym`. -/
theorem h2b2_resolve_dehooked {mpl : MultiPlacement} {sym : String}
    (hsym : sym ∈ cliDehookedSymsPlaced) :
    libsignalSessionLib.resolve mpl sym = mpl.ρ sym := by
  rw [cliDehookedSymsPlaced_eq_entries, List.mem_map] at hsym
  obtain ⟨⟨idx, cs, stubVa, targetVa⟩, hmem_e, rfl⟩ := hsym
  have hmem_pair : (String.ofList cs, targetVa) ∈ h2b2_dehookedTargetPairs := by
    rw [← h2b2_f3DehookedEntries_pairs_eq, List.mem_map]
    exact ⟨(idx, cs, stubVa, targetVa), hmem_e, rfl⟩
  exact (h2b2_dehooked_pair_facts hmem_pair).2.1

theorem h2b2_resolve_shim (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsRustNoAllocShimSymCli = mpl.ρ lsRustNoAllocShimSymCli :=
  (h2b2_dehooked_pair_facts (tgt := f3NoShimV2Addr) (by simp [h2b2_dehookedTargetPairs])).2.1

theorem h2b2_resolve_alloc (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsRustAllocSymCli = mpl.ρ lsRustAllocSymCli :=
  (h2b2_dehooked_pair_facts (tgt := f3StubAddrs.alloc) (by simp [h2b2_dehookedTargetPairs])).2.1

theorem h2b2_resolve_dealloc (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsRustDeallocSymCli = mpl.ρ lsRustDeallocSymCli :=
  (h2b2_dehooked_pair_facts (tgt := f3StubAddrs.dealloc) (by simp [h2b2_dehookedTargetPairs])).2.1

theorem h2b2_resolve_realloc (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsRustReallocSymCli = mpl.ρ lsRustReallocSymCli :=
  (h2b2_dehooked_pair_facts (tgt := f3StubAddrs.realloc) (by simp [h2b2_dehookedTargetPairs])).2.1

theorem h2b2_resolve_allocZeroed (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsRustAllocZeroedSymCli = mpl.ρ lsRustAllocZeroedSymCli :=
  (h2b2_dehooked_pair_facts (tgt := f3StubAzAddr) (by simp [h2b2_dehookedTargetPairs])).2.1

theorem h2b2_resolve_readFile (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsReadFileSym = mpl.ρ lsReadFileSym :=
  (h2b2_dehooked_pair_facts (tgt := 0x4691b4#64) (by simp [h2b2_dehookedTargetPairs])).2.1

theorem h2b2_resolve_readStdin (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsReadStdinSym = mpl.ρ lsReadStdinSym :=
  (h2b2_dehooked_pair_facts (tgt := 0x469000#64) (by simp [h2b2_dehookedTargetPairs])).2.1

/-- Demangled `<alloc::string::String as core::clone::Clone>::clone` resolves to Block `623`
    (`= (hole2_targets mpl).stringClone`). -/
theorem h2b2_resolve_stringClonePlaced (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl lsStringClonePlacedSym = (hole2_targets mpl).stringClone :=
  ls_resolve_stringClone mpl

set_option maxRecDepth 4000000 in
private theorem h2b2_strCloneSym_not_mem_lsNamesB :
    List.elem lsStringCloneSym lsInternedMultiLib.names = false := by
  rfl_kernel

/-- Mangled `lsStringCloneSym` is absent from `(libsignalSessionLib.blockLib 617).text.externs`
(since `<String as Clone>::clone` is intra-library Block `623`). -/
theorem h2b2_strCloneSym_not_mem_ext617 :
    lsStringCloneSym ∉ (libsignalSessionLib.blockLib 617).text.externs := by
  intro hmem
  rw [ls_block617_externs_eq, List.mem_map] at hmem
  obtain ⟨idx, hidx_mem, hget⟩ := hmem
  have hlt : idx < lsInternedMultiLib.names.length :=
    Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx_mem)
  have hmem_names : lsStringCloneSym ∈ lsInternedMultiLib.names := by
    rw [← hget, Obj.Interned.getD_of_lt hlt]
    exact List.getElem_mem hlt
  have htrue : List.elem lsStringCloneSym lsInternedMultiLib.names = true :=
    List.elem_eq_true_of_mem hmem_names
  rw [h2b2_strCloneSym_not_mem_lsNamesB] at htrue
  cases htrue

/-! ## ELF `.symtab` `lookupUnique` Target-VA Identities -/

theorem h2b2_lookupUnique_shim :
    Obj.lookupUnique lsRustNoAllocShimSymCli cliElfImage.symbols = some f3NoShimV2Addr :=
  (h2b2_dehooked_pair_facts (mpl := { base := fun _ => 0#64, ρ := fun _ => 0#64 })
    (by simp [h2b2_dehookedTargetPairs])).2.2

theorem h2b2_lookupUnique_alloc (mpl : MultiPlacement) :
    Obj.lookupUnique lsRustAllocSymCli cliElfImage.symbols = some f3StubAddrs.alloc :=
  (h2b2_dehooked_pair_facts (mpl := mpl) (tgt := f3StubAddrs.alloc)
    (by simp [h2b2_dehookedTargetPairs])).2.2

theorem h2b2_lookupUnique_dealloc (mpl : MultiPlacement) :
    Obj.lookupUnique lsRustDeallocSymCli cliElfImage.symbols = some f3StubAddrs.dealloc :=
  (h2b2_dehooked_pair_facts (mpl := mpl) (tgt := f3StubAddrs.dealloc)
    (by simp [h2b2_dehookedTargetPairs])).2.2

theorem h2b2_lookupUnique_realloc (mpl : MultiPlacement) :
    Obj.lookupUnique lsRustReallocSymCli cliElfImage.symbols = some f3StubAddrs.realloc :=
  (h2b2_dehooked_pair_facts (mpl := mpl) (tgt := f3StubAddrs.realloc)
    (by simp [h2b2_dehookedTargetPairs])).2.2

theorem h2b2_lookupUnique_allocZeroed (mpl : MultiPlacement) :
    Obj.lookupUnique lsRustAllocZeroedSymCli cliElfImage.symbols =
      some f3StubAzAddr :=
  (h2b2_dehooked_pair_facts (mpl := mpl) (tgt := f3StubAzAddr)
    (by simp [h2b2_dehookedTargetPairs])).2.2

theorem h2b2_lookupUnique_readFile (mpl : MultiPlacement) :
    Obj.lookupUnique lsReadFileSym cliElfImage.symbols = some (hole2_targets mpl).readFile :=
  (h2b2_dehooked_pair_facts (mpl := mpl) (tgt := 0x4691b4#64)
    (by simp [h2b2_dehookedTargetPairs])).2.2

theorem h2b2_lookupUnique_readStdin (mpl : MultiPlacement) :
    Obj.lookupUnique lsReadStdinSym cliElfImage.symbols = some (hole2_targets mpl).readStdin :=
  (h2b2_dehooked_pair_facts (mpl := mpl) (tgt := 0x469000#64)
    (by simp [h2b2_dehookedTargetPairs])).2.2

/-! ## `StubReachesTargetOn (F3CodeInv mpl mmpl)` Witnesses -/

/-- Unified `externAt? = none` + `StubReachesTargetOn (F3CodeInv mpl mmpl)` witness for every
    `(sym, tgt) ∈ h2b2_dehookedTargetPairs`. -/
theorem h2b2_dehooked_stubReachesTargetOn {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {sym : String} {tgt : BitVec 64}
    (hmem : (sym, tgt) ∈ h2b2_dehookedTargetPairs) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
      (libsignalSessionLib.resolve mpl sym) = none ∧
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? tgt = none ∧
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl sym) tgt := by
  obtain ⟨hsym, hres, hlu_tgt⟩ := h2b2_dehooked_pair_facts (mpl := mpl) hmem
  obtain ⟨hstub_none, targetVa, hlu_wit, hdir, htgt_none⟩ :=
    h2sl_realW_dehooked_witness (mmpl := mmpl) hLs hsym
  have htgt_eq : targetVa = tgt := Option.some.inj (hlu_wit.symm.trans hlu_tgt)
  subst htgt_eq
  rw [hres]
  refine ⟨hstub_none W, htgt_none W, ?_⟩
  exact stubReachesTargetOn_of_directOrBranchStub (hstub_none W) hdir
    (fun _ hInv => h2b2_unpatched_load hLs hInv)

theorem h2b2_stub_shim {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) :
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl lsRustNoAllocShimSymCli)
      f3NoShimV2Addr :=
  (h2b2_dehooked_stubReachesTargetOn hLs (tgt := f3NoShimV2Addr)
    (by simp [h2b2_dehookedTargetPairs]) W).2.2

private theorem h2b2_thunk_reachesTarget_of_hasInstrs {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) {stubPc stubVa rdlVa : BitVec 64}
    (h0 : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc stubVa)
    (hInstr : ProofLib.StdStartup.hasInstrs f3TrialRxProg stubVa [ .b (rdlVa - stubVa) ])
    (hks : hole2_keepSub stubVa = true) :
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc rdlVa := by
  intro u hpc hrun hfr hInv
  have hsteps0 := h0 u hpc hrun hfr hInv
  have hfetch_rx : f3TrialRxProg.fetch stubVa = some (.b (rdlVa - stubVa)) :=
    ProofLib.StdStartup.hasInstrs.fetch_at_zero hInstr
  have hfm_rx : f3TrialRxProg.fetchMem u.mem stubVa = some (.b (rdlVa - stubVa)) :=
    Program.fetchMem_of_fetch hInv.rxCode hfetch_rx
  have hno_real :
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? stubVa = none :=
    h2sl_realW_noExtern_keepSub hLs mmpl W stubVa hks
  have hno_rx : f3TrialRxProg.externAt? stubVa = none :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext stubVa
  have hfm :
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).fetchMem
        (u.setPC stubVa).mem (u.setPC stubVa).pc = some (.b (rdlVa - stubVa)) := by
    change (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).fetchMem u.mem stubVa =
      some (.b (rdlVa - stubVa))
    unfold Program.fetchMem at hfm_rx ⊢
    rw [hno_real]
    rw [hno_rx] at hfm_rx
    exact hfm_rx
  have hrun1 : (u.setPC stubVa).status = .Running := hrun
  have hstep1 :
      Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (u.setPC stubVa)
        ((cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).evalInst (.b (rdlVa - stubVa))
          (u.setPC stubVa)) :=
    Step.exec hrun1 hfm
  have heval :
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).evalInst (.b (rdlVa - stubVa))
        (u.setPC stubVa) = u.setPC rdlVa := by
    have h1 :
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).evalInst (.b (rdlVa - stubVa))
          (u.setPC stubVa) = (u.setPC stubVa).setPC (stubVa + (rdlVa - stubVa)) := rfl
    rw [h1, show stubVa + (rdlVa - stubVa) = rdlVa by bv_omega]
    cases u
    rfl
  rw [heval] at hstep1
  exact hsteps0.trans (Steps.step hstep1 (Steps.refl _))

theorem h2b2_stub_alloc {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) :
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl lsRustAllocSymCli)
      (hole2_targets mpl).alloc :=
  h2b2_thunk_reachesTarget_of_hasInstrs hLs W
    ((h2b2_dehooked_stubReachesTargetOn hLs (tgt := f3StubAddrs.alloc)
      (by simp [h2b2_dehookedTargetPairs]) W).2.2)
    f3Trial_rustStdThunkCode.alloc_thunk (by decide)

theorem h2b2_stub_dealloc {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) :
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl lsRustDeallocSymCli)
      (hole2_targets mpl).dealloc :=
  h2b2_thunk_reachesTarget_of_hasInstrs hLs W
    ((h2b2_dehooked_stubReachesTargetOn hLs (tgt := f3StubAddrs.dealloc)
      (by simp [h2b2_dehookedTargetPairs]) W).2.2)
    f3Trial_rustStdThunkCode.dealloc_thunk (by decide)

theorem h2b2_stub_realloc {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) :
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl lsRustReallocSymCli)
      (hole2_targets mpl).realloc :=
  h2b2_thunk_reachesTarget_of_hasInstrs hLs W
    ((h2b2_dehooked_stubReachesTargetOn hLs (tgt := f3StubAddrs.realloc)
      (by simp [h2b2_dehookedTargetPairs]) W).2.2)
    f3Trial_rustStdThunkCode.realloc_thunk (by decide)

theorem h2b2_stub_allocZeroed {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) :
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl lsRustAllocZeroedSymCli)
      (hole2_targets mpl).allocZeroed :=
  h2b2_thunk_reachesTarget_of_hasInstrs hLs W
    ((h2b2_dehooked_stubReachesTargetOn hLs (tgt := f3StubAzAddr)
      (by simp [h2b2_dehookedTargetPairs]) W).2.2)
    f3Trial_stubAz_hasInstrs (by decide)

theorem h2b2_stub_readFile {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) :
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl lsReadFileSym)
      (hole2_targets mpl).readFile :=
  (h2b2_dehooked_stubReachesTargetOn hLs (tgt := 0x4691b4#64)
    (by simp [h2b2_dehookedTargetPairs]) W).2.2

theorem h2b2_stub_readStdin {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) :
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl lsReadStdinSym)
      (hole2_targets mpl).readStdin :=
  (h2b2_dehooked_stubReachesTargetOn hLs (tgt := 0x469000#64)
    (by simp [h2b2_dehookedTargetPairs]) W).2.2

theorem h2b2_stub_stringClone_target (mpl mmpl : MultiPlacement) (W : CliHooks) :
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (hole2_targets mpl).stringClone
      (hole2_targets mpl).stringClone :=
  fun u hpc hrun hfr _ => StubReachesTarget.refl _ _ u hpc hrun hfr

theorem h2b2_stub_stringClone (mpl mmpl : MultiPlacement) (W : CliHooks) :
    StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (libsignalSessionLib.resolve mpl lsStringClonePlacedSym)
      (hole2_targets mpl).stringClone := by
  rw [h2b2_resolve_stringClonePlaced]
  exact h2b2_stub_stringClone_target mpl mmpl W

/-! ## `lsRustNoAllocShimSymCli` Replay and `cliGhostExterns` Bridges -/

/-- Under `F3CodeInv mpl mmpl m`, `P_real_W.fetchMem m f3NoShimV2Addr` decodes `.ret .lr`
    (`0xd65f03c0` at `0x469640#64` in `seg[2]`). -/
theorem h2b2_shim_fetchMem_ret {mpl mmpl : MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) (hInv : F3CodeInv mpl mmpl m) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).fetchMem m f3NoShimV2Addr =
      some (.ret .lr) := by
  have hfetch_rx : f3TrialRxProg.fetch f3NoShimV2Addr = some (.ret .lr) :=
    ProofLib.StdStartup.hasInstrs.fetch_at_zero f3Trial_seg5ShimBundle.noAllocShimV2
  have hfm_rx : f3TrialRxProg.fetchMem m f3NoShimV2Addr = some (.ret .lr) :=
    Program.fetchMem_of_fetch hInv.rxCode hfetch_rx
  have hks : hole2_keepSub f3NoShimV2Addr = true := by decide
  have hno_real :
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? f3NoShimV2Addr = none :=
    h2sl_realW_noExtern_keepSub hLs mmpl W f3NoShimV2Addr hks
  have hno_rx : f3TrialRxProg.externAt? f3NoShimV2Addr = none :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext f3NoShimV2Addr
  unfold Program.fetchMem at hfm_rx ⊢
  rw [hno_real]
  rw [hno_rx] at hfm_rx
  exact hfm_rx

/-- Complete branch-2 replay for `lsRustNoAllocShimSymCli` (`hookNoop`): no `lr` guard required,
    stepping directly at `0x469640` (`ret`) = `hookNoop u`. -/
theorem h2b2_shim_branch2 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) (u : State)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsRustNoAllocShimSymCli)
    (hrun : u.status = .Running)
    (hfr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (hookNoop u) ∧
    ExecFrozen (hookNoop u).mem := by
  have hstub := h2b2_stub_shim hLs W u hpc hrun hfr hInv
  have hfm :
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).fetchMem
        (u.setPC f3NoShimV2Addr).mem (u.setPC f3NoShimV2Addr).pc = some (.ret .lr) :=
    h2b2_shim_fetchMem_ret hLs W hInv
  have hrun1 : (u.setPC f3NoShimV2Addr).status = .Running := hrun
  have hstep1 :
      Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (u.setPC f3NoShimV2Addr)
        ((cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).evalInst (.ret .lr)
          (u.setPC f3NoShimV2Addr)) :=
    Step.exec hrun1 hfm
  have heval :
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).evalInst (.ret .lr)
        (u.setPC f3NoShimV2Addr) = hookNoop u := rfl
  rw [heval] at hstep1
  exact ⟨hstub.trans (Steps.step hstep1 (Steps.refl _)), hfr⟩

/-- Base-extern independence of `cliGhostExterns` on every active symbol `(sym, f)` (`GhostSymActive g sym f`):
    `cliGhostExterns g baseExt sym = some f` holds for every `baseExt` (including `cliExternsPlaced mmpl W`
    and `fun _ => none`). -/
theorem h2b2_cliGhostExterns_eq_some_of_active
    (g : CliGhostHooks) (baseExt : String → Option (State → State))
    {sym : String} {f : State → State}
    (hAct : GhostSymActive g sym f) :
    cliGhostExterns g baseExt sym = some f := by
  rcases hAct with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, hsc⟩ | ⟨rfl, hg, hrf⟩ | ⟨rfl, hg, hrs⟩ | ⟨rfl, hms⟩ | ⟨rfl, hmc⟩
  · unfold cliGhostExterns lsRustAllocSymCli; simp
  · unfold cliGhostExterns lsRustDeallocSymCli lsRustAllocSymCli; simp
  · unfold cliGhostExterns lsRustReallocSymCli lsRustAllocSymCli lsRustDeallocSymCli; simp
  · unfold cliGhostExterns lsRustAllocZeroedSymCli lsRustAllocSymCli lsRustDeallocSymCli
      lsRustReallocSymCli; simp
  · unfold cliGhostExterns lsRustNoAllocShimSymCli lsRustAllocSymCli lsRustDeallocSymCli
      lsRustReallocSymCli lsRustAllocZeroedSymCli; simp
  · unfold cliGhostExterns lsStringCloneSym lsRustAllocSymCli lsRustDeallocSymCli
      lsRustReallocSymCli lsRustAllocZeroedSymCli lsRustNoAllocShimSymCli; simp [hsc]
  · unfold cliGhostExterns lsReadFileSym lsRustAllocSymCli lsRustDeallocSymCli
      lsRustReallocSymCli lsRustAllocZeroedSymCli lsRustNoAllocShimSymCli lsStringCloneSym
    simp [hrf]
  · unfold cliGhostExterns lsReadStdinSym lsRustAllocSymCli lsRustDeallocSymCli
      lsRustReallocSymCli lsRustAllocZeroedSymCli lsRustNoAllocShimSymCli lsStringCloneSym
      lsReadFileSym
    simp [hrs]
  · exact cliGhostExterns_memset_some g baseExt hms
  · exact cliGhostExterns_memcpy_some g baseExt hmc

/-- On every active ghost symbol, `cliGhostExterns g (cliExternsPlaced mmpl W) sym` equals
`cliGhostExterns g (fun _ => none) sym`. -/
theorem h2b2_cliGhostExterns_realBase_eq_noneBase_of_active
    (g : CliGhostHooks) (mmpl : MultiPlacement) (W : CliHooks)
    {sym : String} {f : State → State}
    (hAct : GhostSymActive g sym f) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym =
      cliGhostExterns g (fun _ => none) sym := by
  rw [h2b2_cliGhostExterns_eq_some_of_active g (cliExternsPlaced mmpl W) hAct,
    h2b2_cliGhostExterns_eq_some_of_active g (fun _ => none) hAct]

/-- For every `g : CliGhostHooks` and every `sym ∈ (libsignalSessionLib.blockLib 617).text.externs`
    with `GhostSymActive g sym f`, `P_real_W.externAt? (libsignalSessionLib.resolve mpl sym) = none`. -/
theorem h2b2_realW_externAt_none_of_ghostSymActive
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State}
    (hsym_ext : sym ∈ (libsignalSessionLib.blockLib 617).text.externs)
    (hAct : GhostSymActive g sym f) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
      (libsignalSessionLib.resolve mpl sym) = none := by
  rcases hAct with
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact (h2b2_dehooked_stubReachesTargetOn hLs (tgt := f3StubAddrs.alloc)
      (by simp [h2b2_dehookedTargetPairs]) W).1
  · exact (h2b2_dehooked_stubReachesTargetOn hLs (tgt := f3StubAddrs.dealloc)
      (by simp [h2b2_dehookedTargetPairs]) W).1
  · exact (h2b2_dehooked_stubReachesTargetOn hLs (tgt := f3StubAddrs.realloc)
      (by simp [h2b2_dehookedTargetPairs]) W).1
  · exact (h2b2_dehooked_stubReachesTargetOn hLs (tgt := f3StubAzAddr)
      (by simp [h2b2_dehookedTargetPairs]) W).1
  · exact (h2b2_dehooked_stubReachesTargetOn hLs (tgt := f3NoShimV2Addr)
      (by simp [h2b2_dehookedTargetPairs]) W).1
  · exact False.elim (h2b2_strCloneSym_not_mem_ext617 hsym_ext)
  · exact (h2b2_dehooked_stubReachesTargetOn hLs (tgt := 0x4691b4#64)
      (by simp [h2b2_dehookedTargetPairs]) W).1
  · exact (h2b2_dehooked_stubReachesTargetOn hLs (tgt := 0x469000#64)
      (by simp [h2b2_dehookedTargetPairs]) W).1
  · exact (h2b2_dehooked_stubReachesTargetOn hLs (tgt := wp4MemsetRealAddr)
      (by simp [h2b2_dehookedTargetPairs]) W).1
  · exact (h2b2_dehooked_stubReachesTargetOn hLs (tgt := wp4MemcpyRealAddr)
      (by simp [h2b2_dehookedTargetPairs]) W).1

/-! ## Non-`.Exception` Guard Extraction and First-Stop Bundle -/

/-- Unwrap `ActiveF3CallPre` over `h2k_withKeepLrFalse` into `ActiveF3CallPre specOf` and
    `keepSet (s.readReg64 .lr) = false`. -/
theorem h2b2_activeF3CallPre_withKeepLrFalse {α : Type}
    {keepSet : BitVec 64 → Bool} {specOf : GhostName → BitVec 64 → Spec α} {s : State}
    (h : ActiveF3CallPre (fun γ tp => h2k_withKeepLrFalse keepSet (specOf γ tp)) s) :
    ActiveF3CallPre specOf s ∧ keepSet (s.readReg64 .lr) = false := by
  obtain ⟨hrun, hsp, γ, tp, x, R, hSat⟩ := h
  dsimp only [h2k_withKeepLrFalse] at hSat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hSat
  exact ⟨⟨hrun, hsp, γ, tp, x, R, hSat.2⟩, hSat.1⟩

/-- Unwrap `ActiveF3CallPre` over `h2k_withKeepLrAndFds` into `ActiveF3CallPre specOf`,
    `keepSet (s.readReg64 .lr) = false`, and `FdsGe3Closed s.fs`. -/
theorem h2b2_activeF3CallPre_withKeepLrAndFds {α : Type}
    {keepSet : BitVec 64 → Bool} {specOf : GhostName → BitVec 64 → Spec α} {s : State}
    (h : ActiveF3CallPre (fun γ tp => h2k_withKeepLrAndFds keepSet (specOf γ tp)) s) :
    ActiveF3CallPre specOf s ∧ keepSet (s.readReg64 .lr) = false ∧ FdsGe3Closed s.fs := by
  obtain ⟨hrun, hsp, γ, tp, x, R, hSat⟩ := h
  dsimp only [h2k_withKeepLrAndFds] at hSat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hSat
  exact ⟨⟨hrun, hsp, γ, tp, x, R, hSat.2⟩, hSat.1.1, hSat.1.2⟩

theorem h2b2_keepSub_false_of_keep_false {a : BitVec 64}
    (h : hole2_keep a = false) : hole2_keepSub a = false := by
  cases hks : hole2_keepSub a with
  | false => rfl
  | true =>
    have hbounds : 0x469000 ≤ a.toNat ∧ a.toNat < 0x46f000 := of_decide_eq_true hks
    have hk : hole2_keep a = true := decide_eq_true (Or.inr hbounds)
    rw [hk] at h
    cases h

private theorem h2b2_activeF3CallPre_of_f3LinkedCallHook_noException {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {fallback : State → State} {a : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback a).status ≠ .Exception msg) :
    ActiveF3CallPre specOf a := by
  classical
  by_contra hn
  apply hnoex "ghost-hook precondition violated"
  unfold f3LinkedCallHook
  simp [hn]

/-- Non-`.Exception` `hole2_keep` `lr`-guard extraction (via `h2k_keepLr_false_of_noException`). -/
theorem h2b2_keepLr_false_of_noException [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {sym : String} {f : State → State} {a : State}
    (hext : cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f)
    (hnoShim : sym ≠ lsRustNoAllocShimSymCli)
    (hnoex : ∀ msg, (f a).status ≠ .Exception msg)
    (hnoMs : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (hnoMc : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    h2k_keepSetForSym sym (a.readReg64 .lr) = false :=
  h2k_keepLr_false_of_noException mpl mmpl hext hnoShim hnoex hnoMs hnoMc

/-- Non-`.Exception` `hole2_keepSub` `lr`-guard extraction (via
`h2k_keepSubLr_false_of_noException`). -/
theorem h2b2_keepSubLr_false_of_noException [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {sym : String} {f : State → State} {a : State}
    (hext : cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f)
    (hnoShim : sym ≠ lsRustNoAllocShimSymCli)
    (hnoex : ∀ msg, (f a).status ≠ .Exception msg)
    (hnoMs : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (hnoMc : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    hole2_keepSub (a.readReg64 .lr) = false :=
  h2k_keepSubLr_false_of_noException mpl mmpl hext hnoShim hnoex hnoMs hnoMc

/-- Non-`.Exception` `FdsGe3Closed` extraction for `lsReadFileSym` (via
`h2k_fds_of_noException`). -/
theorem h2b2_fds_of_noException [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {baseExt : String → Option (State → State)} {f : State → State} {a : State}
    (hext : cliGhostExterns (h2k_ghFixedK mpl mmpl) baseExt lsReadFileSym = some f)
    (hnoex : ∀ msg, (f a).status ≠ .Exception msg) :
    FdsGe3Closed a.fs :=
  h2k_fds_of_noException mpl mmpl hext hnoex

/-- `ActiveRealRun` statement for `alloc` on `hole2_keepSub`. -/
def h2b2_R_Alloc [LibsignalPlacement] (mmpl : MultiPlacement) : Prop :=
  ∀ {s0 : State},
    ActiveF3CallPre
      (fun γ tp => rustCliAllocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits false) s0 →
    ExecFrozen s0.mem →
    hole2_keepSub (s0.readReg64 .lr) = false →
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) →
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.alloc s0

/-- `ActiveRealRun` statement for `allocZeroed` on `hole2_keepSub`. -/
def h2b2_R_AllocZeroed [LibsignalPlacement] (mmpl : MultiPlacement) : Prop :=
  ∀ {s0 : State},
    ActiveF3CallPre
      (fun γ tp => rustCliAllocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits true) s0 →
    ExecFrozen s0.mem →
    hole2_keepSub (s0.readReg64 .lr) = false →
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) →
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAzAddr s0

/-- `ActiveRealRun` statement for `dealloc` on `hole2_keepSub`. -/
def h2b2_R_Dealloc [LibsignalPlacement] (mmpl : MultiPlacement) : Prop :=
  ∀ {s0 : State},
    ActiveF3CallPre
      (fun γ tp => rustCliDeallocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits) s0 →
    ExecFrozen s0.mem →
    hole2_keepSub (s0.readReg64 .lr) = false →
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) →
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.dealloc s0

/-- `ActiveRealRun` statement for `realloc` on `hole2_keepSub`. -/
def h2b2_R_Realloc [LibsignalPlacement] (mmpl : MultiPlacement) : Prop :=
  ∀ {s0 : State},
    ActiveF3CallPre (h2fsrealloc_spec mmpl) s0 →
    ExecFrozen s0.mem →
    hole2_keepSub (s0.readReg64 .lr) = false →
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) →
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.realloc s0

theorem h2b2_r_realloc_proven [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    h2b2_R_Realloc mmpl :=
  fun hPre hFr hLr hCode => h2fsrealloc_activeRealRun mmpl hMm hPre hFr hLr hCode

/-- `ActiveF3ReadFileRun` statement for `readFile` on `hole2_keepSub`. -/
def h2b2_R_ReadFile (mmpl : MultiPlacement) : Prop :=
  ∀ {s0 : State},
    ActiveF3CallPre
      (fun γ tp => readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) s0 →
    ExecFrozen s0.mem →
    hole2_keepSub (s0.readReg64 .lr) = false →
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) →
    FdsGe3Closed s0.fs →
    ActiveF3ReadFileRun hole2_keepSub hole2_emptyProg f3TrialRxProg
      0x4691b4#64 F3ReadFileFixedCallGuard s0

/-- `ActiveReadStdinLinkedRun` statement for `readStdin` on `hole2_keepSub`. -/
def h2b2_R_ReadStdin [LibsignalPlacement] (mmpl : MultiPlacement) : Prop :=
  ∀ {s0 : State},
    ActiveF3CallPre
      (fun γ tp => readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv) s0 →
    ExecFrozen s0.mem →
    hole2_keepSub (s0.readReg64 .lr) = false →
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) →
    ActiveReadStdinLinkedRun hole2_keepSub hole2_emptyProg f3TrialRxProg 0x469000#64 s0

/-- 6-field bundle of Block-`617` first-stop witnesses (`alloc`, `allocZeroed`, `dealloc`,
`realloc`, `readFile`, `readStdin`). -/
structure h2b2_AllFirstStopHyps [LibsignalPlacement] (_mpl mmpl : MultiPlacement) : Prop where
  alloc : h2b2_R_Alloc mmpl
  allocZeroed : h2b2_R_AllocZeroed mmpl
  dealloc : h2b2_R_Dealloc mmpl
  realloc : h2b2_R_Realloc mmpl
  readFile : h2b2_R_ReadFile mmpl
  readStdin : h2b2_R_ReadStdin mmpl

theorem h2b2_AllFirstStopHyps.of_five [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hAlloc : h2b2_R_Alloc mmpl)
    (hAz : h2b2_R_AllocZeroed mmpl)
    (hDealloc : h2b2_R_Dealloc mmpl)
    (hReadFile : h2b2_R_ReadFile mmpl)
    (hReadStdin : h2b2_R_ReadStdin mmpl) :
    h2b2_AllFirstStopHyps mpl mmpl :=
  ⟨hAlloc, hAz, hDealloc, h2b2_r_realloc_proven mmpl hMm, hReadFile, hReadStdin⟩

/-! ## Stock-Clean Per-Address Branch-2 Replay Lemmas on `h2k_ghFixedK` (`*_perPc`, Zero `[0, 0, 0, 0]` Stub Check) -/

/-- Stock-clean per-address replacement for `h2b2_branch2_f3LinkedCallHook` via
    `h2sl_stepsUntil_emptyProg_to_realW_of_allProg` (zero `h2sl_checkCompactZeroRxB` dependency). -/
theorem h2b2_branch2_f3LinkedCallHook_perPc {α β : Type}
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks)
    {stubPc entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α}
    {specOf' : GhostName → BitVec 64 → Spec β}
    {fallback : State → State}
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc entryTarget)
    (hPreImp : ∀ s : State, ActiveF3CallPre specOf' s → ActiveF3CallPre specOf s)
    (hR_allProg : ∀ {s0 : State},
      ActiveF3CallPre specOf s0 →
      ExecFrozen s0.mem →
      hole2_keepSub (s0.readReg64 .lr) = false →
      f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) →
      ∀ (P : Program), P.svc = Syscall.standard →
        (∀ pc : BitVec 64, hole2_keepSub pc = true → P.externAt? pc = none) →
        ∃ sf : State,
          StepsUntil P (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
          SubroutineStop s0 sf ∧
          sf.fs = s0.fs ∧
          FsTraced IsFsC s0 sf ∧
          ExecFrozen sf.mem)
    {u : State}
    (hpc : u.pc = stubPc)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg entryTarget specOf' fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    let f := f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg entryTarget specOf' fallback
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
      ExecFrozen (f u).mem ∧
      F3CodeInv mpl mmpl (f u).mem ∧
      (f u).fs = u.fs := by
  classical
  dsimp only
  have hActPre' : ActiveF3CallPre specOf' u :=
    h2b2_activeF3CallPre_of_f3LinkedCallHook_noException hnoex
  have hCodeRx : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub u.mem) :=
    h2cl_f3CodeInv_rxProg_keepSub hInv
  have hAll := hR_allProg (hPreImp u hActPre') hFr hlr hCodeRx
  have hReal : ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg entryTarget u :=
    ⟨hFr, hlr, hCodeRx, hAll hole2_emptyProg h2sl_emptyProg_svc (fun pc _ => h2sl_emptyProg_externAt pc)⟩
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hfu :
      f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg entryTarget specOf' fallback u =
        Classical.choose hReal.2.2.2 := by
    unfold f3LinkedCallHook
    simp only [hActPre', hReal, ↓reduceDIte]
  have hBody :
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC entryTarget) (Classical.choose hReal.2.2.2) :=
    h2sl_stepsUntil_emptyProg_to_realW_of_allProg hLs W
      (fun Q hsvc hno =>
        let ⟨sf, huQ, hsQ, _⟩ := hAll Q hsvc hno
        ⟨sf, huQ, hsQ⟩)
      hchoose.1
  have hkf : u.mem.KeepsFrozen (Classical.choose hReal.2.2.2).mem := by
    simpa only [State.setPC] using hchoose.1.toSteps.keepsFrozen
  rw [hfu]
  exact ⟨(hStub u hpc hrun hFr hInv).trans hBody,
    hchoose.2.2.2.2,
    hInv.of_keepsFrozen hkf,
    hchoose.2.2.1⟩

/-- Stock-clean explicit-`lr` `alloc` branch-2 replay on `(h2k_ghFixedK mpl mmpl).alloc`. -/
theorem h2b2_branch2_alloc_explicitLr_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsRustAllocSymCli)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, ((h2k_ghFixedK mpl mmpl).alloc u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u ((h2k_ghFixedK mpl mmpl).alloc u) ∧
      ExecFrozen ((h2k_ghFixedK mpl mmpl).alloc u).mem ∧
      F3CodeInv mpl mmpl ((h2k_ghFixedK mpl mmpl).alloc u).mem ∧
      ((h2k_ghFixedK mpl mmpl).alloc u).fs = u.fs :=
  h2b2_branch2_f3LinkedCallHook_perPc hLs W (h2b2_stub_alloc hLs W)
    (fun _ h => (h2b2_activeF3CallPre_withKeepLrFalse h).1)
    (fun hPre hFr' hLr' hCode' _P hsvc hno =>
      h2fsalloc_alloc_firstStop_keepSub mmpl hMm hsvc hno hPre hLr' hFr' hCode')
    hpc hrun hnoex hFr hlr hInv

/-- Stock-clean K-hook `alloc` branch-2 replay on `(h2k_ghFixedK mpl mmpl).alloc`. -/
theorem h2b2_branch2_alloc_kHook_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsRustAllocSymCli)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, ((h2k_ghFixedK mpl mmpl).alloc u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u ((h2k_ghFixedK mpl mmpl).alloc u) ∧
      ExecFrozen ((h2k_ghFixedK mpl mmpl).alloc u).mem ∧
      F3CodeInv mpl mmpl ((h2k_ghFixedK mpl mmpl).alloc u).mem ∧
      ((h2k_ghFixedK mpl mmpl).alloc u).fs = u.fs := by
  have hext0 :
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) lsRustAllocSymCli =
        some (h2k_ghFixedK mpl mmpl).alloc :=
    h2b2_cliGhostExterns_eq_some_of_active (h2k_ghFixedK mpl mmpl) (fun _ => none) (Or.inl ⟨rfl, rfl⟩)
  have hlr : hole2_keepSub (u.readReg64 .lr) = false :=
    h2k_keepSubLr_false_of_noException mpl mmpl hext0 (by decide) hnoex
  exact h2b2_branch2_alloc_explicitLr_perPc hLs hMm W hpc hrun hnoex hFr hlr hInv

/-- Stock-clean explicit-`lr` `allocZeroed` branch-2 replay on `(h2k_ghFixedK mpl mmpl).allocZeroed`. -/
theorem h2b2_branch2_allocZeroed_explicitLr_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsRustAllocZeroedSymCli)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, ((h2k_ghFixedK mpl mmpl).allocZeroed u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u ((h2k_ghFixedK mpl mmpl).allocZeroed u) ∧
      ExecFrozen ((h2k_ghFixedK mpl mmpl).allocZeroed u).mem ∧
      F3CodeInv mpl mmpl ((h2k_ghFixedK mpl mmpl).allocZeroed u).mem ∧
      ((h2k_ghFixedK mpl mmpl).allocZeroed u).fs = u.fs :=
  h2b2_branch2_f3LinkedCallHook_perPc hLs W (h2b2_stub_allocZeroed hLs W)
    (fun _ h => (h2b2_activeF3CallPre_withKeepLrFalse h).1)
    (fun hPre hFr' hLr' hCode' _P hsvc hno =>
      h2fsalloc_allocZeroed_firstStop_keepSub mmpl hMm hsvc hno hPre hLr' hFr' hCode')
    hpc hrun hnoex hFr hlr hInv

/-- Stock-clean K-hook `allocZeroed` branch-2 replay on `(h2k_ghFixedK mpl mmpl).allocZeroed`. -/
theorem h2b2_branch2_allocZeroed_kHook_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsRustAllocZeroedSymCli)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, ((h2k_ghFixedK mpl mmpl).allocZeroed u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u ((h2k_ghFixedK mpl mmpl).allocZeroed u) ∧
      ExecFrozen ((h2k_ghFixedK mpl mmpl).allocZeroed u).mem ∧
      F3CodeInv mpl mmpl ((h2k_ghFixedK mpl mmpl).allocZeroed u).mem ∧
      ((h2k_ghFixedK mpl mmpl).allocZeroed u).fs = u.fs := by
  have hext0 :
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) lsRustAllocZeroedSymCli =
        some (h2k_ghFixedK mpl mmpl).allocZeroed :=
    h2b2_cliGhostExterns_eq_some_of_active (h2k_ghFixedK mpl mmpl) (fun _ => none)
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have hlr : hole2_keepSub (u.readReg64 .lr) = false :=
    h2k_keepSubLr_false_of_noException mpl mmpl hext0 (by decide) hnoex
  exact h2b2_branch2_allocZeroed_explicitLr_perPc hLs hMm W hpc hrun hnoex hFr hlr hInv

/-- Stock-clean explicit-`lr` `dealloc` branch-2 replay on `(h2k_ghFixedK mpl mmpl).dealloc`. -/
theorem h2b2_branch2_dealloc_explicitLr_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsRustDeallocSymCli)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, ((h2k_ghFixedK mpl mmpl).dealloc u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u ((h2k_ghFixedK mpl mmpl).dealloc u) ∧
      ExecFrozen ((h2k_ghFixedK mpl mmpl).dealloc u).mem ∧
      F3CodeInv mpl mmpl ((h2k_ghFixedK mpl mmpl).dealloc u).mem ∧
      ((h2k_ghFixedK mpl mmpl).dealloc u).fs = u.fs :=
  h2b2_branch2_f3LinkedCallHook_perPc hLs W (h2b2_stub_dealloc hLs W)
    (fun _ h => (h2b2_activeF3CallPre_withKeepLrFalse h).1)
    (fun hPre hFr' hLr' hCode' _P hsvc hno =>
      h2fsdealloc_firstStop_keepSub mmpl hMm hsvc hno hPre hLr' hFr' hCode')
    hpc hrun hnoex hFr hlr hInv

/-- Stock-clean K-hook `dealloc` branch-2 replay on `(h2k_ghFixedK mpl mmpl).dealloc`. -/
theorem h2b2_branch2_dealloc_kHook_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsRustDeallocSymCli)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, ((h2k_ghFixedK mpl mmpl).dealloc u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u ((h2k_ghFixedK mpl mmpl).dealloc u) ∧
      ExecFrozen ((h2k_ghFixedK mpl mmpl).dealloc u).mem ∧
      F3CodeInv mpl mmpl ((h2k_ghFixedK mpl mmpl).dealloc u).mem ∧
      ((h2k_ghFixedK mpl mmpl).dealloc u).fs = u.fs := by
  have hext0 :
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) lsRustDeallocSymCli =
        some (h2k_ghFixedK mpl mmpl).dealloc :=
    h2b2_cliGhostExterns_eq_some_of_active (h2k_ghFixedK mpl mmpl) (fun _ => none)
      (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hlr : hole2_keepSub (u.readReg64 .lr) = false :=
    h2k_keepSubLr_false_of_noException mpl mmpl hext0 (by decide) hnoex
  exact h2b2_branch2_dealloc_explicitLr_perPc hLs hMm W hpc hrun hnoex hFr hlr hInv

/-- Stock-clean explicit-`lr` `realloc` branch-2 replay on `(h2k_ghFixedK mpl mmpl).realloc`. -/
theorem h2b2_branch2_realloc_explicitLr_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsRustReallocSymCli)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, ((h2k_ghFixedK mpl mmpl).realloc u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u ((h2k_ghFixedK mpl mmpl).realloc u) ∧
      ExecFrozen ((h2k_ghFixedK mpl mmpl).realloc u).mem ∧
      F3CodeInv mpl mmpl ((h2k_ghFixedK mpl mmpl).realloc u).mem ∧
      ((h2k_ghFixedK mpl mmpl).realloc u).fs = u.fs :=
  h2b2_branch2_f3LinkedCallHook_perPc hLs W (h2b2_stub_realloc hLs W)
    (fun _ h => (h2b2_activeF3CallPre_withKeepLrFalse h).1)
    (fun hPre hFr' hLr' hCode' _P hsvc hno =>
      h2fsrealloc_firstStop_of_keep mmpl hMm (h2fsrealloc_keepSub_mallocng mmpl hMm)
        hsvc hno hPre hFr' hLr' hCode')
    hpc hrun hnoex hFr hlr hInv

/-- Stock-clean K-hook `realloc` branch-2 replay on `(h2k_ghFixedK mpl mmpl).realloc`. -/
theorem h2b2_branch2_realloc_kHook_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsRustReallocSymCli)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, ((h2k_ghFixedK mpl mmpl).realloc u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u ((h2k_ghFixedK mpl mmpl).realloc u) ∧
      ExecFrozen ((h2k_ghFixedK mpl mmpl).realloc u).mem ∧
      F3CodeInv mpl mmpl ((h2k_ghFixedK mpl mmpl).realloc u).mem ∧
      ((h2k_ghFixedK mpl mmpl).realloc u).fs = u.fs := by
  have hext0 :
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) lsRustReallocSymCli =
        some (h2k_ghFixedK mpl mmpl).realloc :=
    h2b2_cliGhostExterns_eq_some_of_active (h2k_ghFixedK mpl mmpl) (fun _ => none)
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have hlr : hole2_keepSub (u.readReg64 .lr) = false :=
    h2k_keepSubLr_false_of_noException mpl mmpl hext0 (by decide) hnoex
  exact h2b2_branch2_realloc_explicitLr_perPc hLs hMm W hpc hrun hnoex hFr hlr hInv

/-- Stock-clean explicit-`lr` & explicit-`FdsGe3Closed` `readFile` branch-2 replay on
    `h2k_readFileFixedGhostHookFineK`. -/
theorem h2b2_branch2_readFile_explicitLr_perPc {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsReadFileSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hFds : FdsGe3Closed u.fs)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    let f := h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
      (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
      ExecFrozen (f u).mem ∧
      F3CodeInv mpl mmpl (f u).mem ∧
      (f u).fs = u.fs := by
  classical
  dsimp only
  have hActPre' : ActiveF3CallPre
      (fun γ tp => h2k_readFileAnySpecK
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) u := by
    by_contra hn
    apply hnoex "read_file ghost-hook precondition violated"
    unfold h2k_readFileFixedGhostHookFineK
    simp [hn]
  have hActPre := (h2b2_activeF3CallPre_withKeepLrAndFds hActPre').1
  have hCodeRx : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub u.mem) :=
    h2cl_f3CodeInv_rxProg_keepSub hInv
  have hReal :
      ActiveF3ReadFileRun hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readFile F3ReadFileFixedCallGuard u :=
    h2fsreads_readFile_activeRealRun_keepSub mmpl hMm hActPre hFr hlr hCodeRx hFds
  have hchoose := Classical.choose_spec hReal.2.2.2.2
  have hfu :
      h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
          (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u =
        Classical.choose hReal.2.2.2.2 := by
    unfold h2k_readFileFixedGhostHookFineK
    simp only [hActPre', hReal, ↓reduceDIte]
  have hBody :
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (hole2_targets mpl).readFile) (Classical.choose hReal.2.2.2.2) :=
    h2sl_stepsUntil_emptyProg_to_realW_of_allProg hLs W
      (fun Q hsvc hno =>
        let ⟨sf, huQ, hsQ, _⟩ :=
          h2fsreads_readFile_firstStop_keepSub (P := Q) hMm hsvc hno hActPre hlr hFr hCodeRx hFds
        ⟨sf, huQ, hsQ⟩)
      hchoose.1
  have hkf : u.mem.KeepsFrozen (Classical.choose hReal.2.2.2.2).mem := by
    simpa only [State.setPC] using hchoose.1.toSteps.keepsFrozen
  rw [hfu]
  exact ⟨(h2b2_stub_readFile hLs W u hpc hrun hFr hInv).trans hBody,
    hchoose.2.2.2.2,
    hInv.of_keepsFrozen hkf,
    hchoose.2.2.1⟩

/-- Stock-clean K-hook `readFile` branch-2 replay on `h2k_readFileFixedGhostHookFineK`. -/
theorem h2b2_branch2_readFile_kHook_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsReadFileSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    let f := h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
      (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
      ExecFrozen (f u).mem ∧
      F3CodeInv mpl mmpl (f u).mem ∧
      (f u).fs = u.fs := by
  have hext0 :
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) lsReadFileSym =
        some (h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
          (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack) :=
    h2b2_cliGhostExterns_eq_some_of_active (h2k_ghFixedK mpl mmpl) (fun _ => none)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        (h2k_readFileFixedGhostHookFineSubK hole2_keepSub hole2_emptyProg f3TrialRxProg
          (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack).2,
        rfl⟩)))))))
  have hlr : hole2_keepSub (u.readReg64 .lr) = false :=
    h2k_keepSubLr_false_of_noException mpl mmpl hext0 (by decide) hnoex
  have hFds : FdsGe3Closed u.fs :=
    h2k_fds_of_noException mpl mmpl hext0 hnoex
  exact h2b2_branch2_readFile_explicitLr_perPc hLs hMm W hpc hrun hnoex hFr hlr hFds hInv

/-- Stock-clean explicit-`lr` `readStdin` branch-2 replay on `h2k_readStdinGhostHookFineK`. -/
theorem h2b2_branch2_readStdin_explicitLr_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsReadStdinSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (h2k_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    let f := h2k_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
      (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
      ExecFrozen (f u).mem ∧
      F3CodeInv mpl mmpl (f u).mem ∧
      (FdsGe3Closed u.fs → FdsGe3Closed (f u).fs) := by
  classical
  dsimp only
  have hActPre' : ActiveF3CallPre
      (fun γ tp => h2k_readStdinSpecK cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv) u := by
    by_contra hn
    apply hnoex "read_stdin ghost-hook precondition violated"
    unfold h2k_readStdinGhostHookFineK
    simp [hn]
  have hActPre := (h2b2_activeF3CallPre_withKeepLrFalse hActPre').1
  have hCodeRx : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub u.mem) :=
    h2cl_f3CodeInv_rxProg_keepSub hInv
  have hReal :
      ActiveReadStdinLinkedRun hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin u :=
    h2fsreads_readStdin_activeRealRun_keepSub mmpl hMm hActPre hFr hlr hCodeRx
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hfu :
      h2k_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
          (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u =
        Classical.choose hReal.2.2.2 := by
    unfold h2k_readStdinGhostHookFineK
    simp only [hActPre', hReal, ↓reduceDIte]
  have hBody :
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (hole2_targets mpl).readStdin) (Classical.choose hReal.2.2.2) :=
    h2sl_stepsUntil_emptyProg_to_realW_of_allProg hLs W
      (fun Q hsvc hno =>
        let ⟨sf, huQ, hsQ, _⟩ :=
          h2fsreads_readStdin_firstStop_keepSub (P := Q) hMm hsvc hno hActPre hlr hFr hCodeRx
        ⟨sf, huQ, hsQ⟩)
      hchoose.1
  have hkf : u.mem.KeepsFrozen (Classical.choose hReal.2.2.2).mem := by
    simpa only [State.setPC] using hchoose.1.toSteps.keepsFrozen
  rw [hfu]
  exact ⟨(h2b2_stub_readStdin hLs W u hpc hrun hFr hInv).trans hBody,
    hchoose.2.2.2.2.2,
    hInv.of_keepsFrozen hkf,
    hchoose.2.2.2.2.1⟩

/-- Stock-clean K-hook `readStdin` branch-2 replay on `h2k_readStdinGhostHookFineK`. -/
theorem h2b2_branch2_readStdin_kHook_perPc [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsReadStdinSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (h2k_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    let f := h2k_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
      (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
      ExecFrozen (f u).mem ∧
      F3CodeInv mpl mmpl (f u).mem ∧
      (FdsGe3Closed u.fs → FdsGe3Closed (f u).fs) := by
  have hext0 :
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) lsReadStdinSym =
        some (h2k_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
          (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack) :=
    h2b2_cliGhostExterns_eq_some_of_active (h2k_ghFixedK mpl mmpl) (fun _ => none)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        (h2k_readStdinGhostHookFineSubK hole2_keepSub hole2_emptyProg f3TrialRxProg
          (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack).2,
        rfl⟩))))))))
  have hlr : hole2_keepSub (u.readReg64 .lr) = false :=
    h2k_keepSubLr_false_of_noException mpl mmpl hext0 (by decide) hnoex
  exact h2b2_branch2_readStdin_explicitLr_perPc hLs hMm W hpc hrun hnoex hFr hlr hInv

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Branch2
