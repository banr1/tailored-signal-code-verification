/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLifts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLiftsPcs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget -- proof-setup: allow-public-import

/-!
# Ghost-`memcpy` / `memset` `BaseHelperRowsSat` & `HookSat` Discharge Bundle (`CliMemcpyRowSat`)

Cone 4 Wave 1 (`#1255` L5) row-satisfaction adapters replacing hook-identity equalities
(`baseExt memcpyName = cliExternsPlaced mmpl W memcpyName`,
`baseExt memsetName = cliExternsPlaced mmpl W memsetName`) with contract-level row bundles
(`GhostMemcpyRow`, `GhostMemsetRow`, `BaseHelperRowsSat`), while keeping `memmove_eq` untouched:

1. **`MemcpyStripKeepsFrozen` Ghost Bridges:** `memcpyStripKeepsFrozen_linkedCallHook`,
   `memcpyStripKeepsFrozen_memcpyGhostHook`, and `memcpyStripKeepsFrozen_memcpyGhostHookK` for
   `CodecCalleesFsTransferPlacedBudgetFd`'s `codec_pure_fs_transfer_at_579_mc`.
2. **`GhostMemcpyRow`, `GhostMemsetRow`, & `BaseHelperRowsSat`:** Row predicates, constructors from
   both stock `hookMemcpy` / `hookMemset` (`BaseHelperRows.toSat`) and `memcpyGhostHook` /
   `memsetGhostHook`, and `cliGhostExterns` preservation.
3. **`HookSat` Discharge Suite:** Discharges all shared CLI/Stage2/Codec `memcpy` & `memset`
   contracts and all `WP6a-mc1` (`MemcpyGhostLifts` + `MemcpyGhostLiftsPcs`) file-local `memcpy`
   contracts directly from `GhostMemcpyRow` / `GhostMemsetRow`.
4. **Bundle & Pure-`fs` Codec Adapters:** `allocContractsXCliPlaced_of_ghost_sat`,
   `allocContractsFsPlaced_of_ghost_sat`, `stage2ContractsMinPlaced_of_ghost_sat`,
   `codecHooksPlaced_of_ghost_sat`, `publicApiDecHooksPlaced_of_ghost_sat`, and the `_of_sat`
   Block `85` (`tryFrom`) / Block `111` (`pksmSlot`) pure-`fs` transfer corollaries.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliMemcpyRowSat

open Arm64 ProofLib SepProp
open VerifiedLibraries.Musl (memcpySymWords memsetWordsSym)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPl_111 lsHandleErrorSym lsmpl
)
open CryptoVerification.E2E.Bin (openMemcpyRoSpec openMemcpySpec)
open CryptoVerification.E2E.InMem.HashbrownBin.FallibleWithCapacity (hashbrownMemcpyRegionSpec)
open CryptoVerification.E2E.Pqxdh.Initiator (pqxdhMemcpyRegionSpec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (lsExpectFailedSym)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack framelessMemcpySpec memcpyName memcpyROExtSpec memmoveName memsetName
  sessionMemcpyROXSpec sessionMemcpyRegionSpec sessionMemcpySpec
  sessionMemsetRegionSpec sessionMemsetSpec withStack
)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (session2MemsetExternSpec)
open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty (
  memcpyRecvPcsSpec memcpyRecvPcsSpecS
)
open CryptoVerification.LibsignalTripleRatchet.Prost (lsHandleAllocErrorSym)
open CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty (memcpyPcsSpec)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsFromUtf8Sym lsMemrchrSym lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliExternsPlaced_memcpy_none cliExternsPlaced_memset_none
  hookMemcpy_fs hookMemmove_fs hookMemset_fs hookNoop_fs hookOk_withStack
)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks IsFsC cliExternsPlaced_row cliGhostExterns cliGhostExterns_alloc
  cliGhostExterns_dealloc cliGhostExterns_memcpy_none cliGhostExterns_memcpy_some
  cliGhostExterns_memset_none cliGhostExterns_memset_some cliGhostExterns_other
  cliGhostExterns_realloc cliGhostExterns_shim hookMemcpy_fsT hookMemset_fsT hookSat_of_eq
)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.Slots (
  memmove_row_placed
)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (CliPanicHooksPlaced)
open CryptoVerification.SignalSession.CliExt (memcpyROSpec memcpySpec memsetSpec)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits MallocngCostModelIface MallocngCostModelSound
  RustCliAllocBudget VmPreserved allocMemcpyVmSpec
)
open LibsignalBinary.Heap.Fine (
  fineCostModel hookMemcpy_vmPreserved hookMemset_vmPreserved
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  fineHookRustCliAllocBudget mallocngHookRustCliAllocBudget
)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (PublicApiDecHooksPlaced)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget (Stage2ContractsMinPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun BaseHelperRows CliGhostAllocHooks cliGhostExterns_panics
  keepFsTrace linkedCallHook linkedCallHook_fs linkedCallHook_fsT
  noAllocShim_budget_sat_of_eq shim_budget_sat_of_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  hookMemcpy_masterMemcpy_ok hookOk_allocMemcpyVm_of_master hookOk_cliMemcpyRO_of_master
  hookOk_cliMemcpy_of_master hookOk_framelessMemcpy_of_master hookOk_libcMemcpy_of_master
  hookOk_memcpyROExt_of_master hookOk_memcpyRegion_of_master hookOk_sessionMemcpyRO4K_of_master
  hookOk_sessionMemcpyRegionRO_of_master hookOk_sessionMemcpyRegion_of_master
  hookOk_sessionMemcpy_of_master masterMemcpySpec memcpySpecK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  memcpyGhostHook memcpyGhostHookK memcpyGhostHook_master_ok memcpyGhostHook_oracle
  memcpyGhostHook_vmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLifts (
  hookOk_chainClone3SessionMemcpyBudget_of_master hookOk_chainClone3SessionMemcpy_of_master
  hookOk_hashbrownMemcpyRegion_of_master hookOk_openMemcpyRo_of_master hookOk_openMemcpy_of_master
  hookOk_pqxdhMemcpyRegion_of_master hookOk_recordSessionCloneMemcpy_of_master
  hookOk_rustStdAllocMemcpyVm_of_master hookOk_sessionMemcpyROX_of_master
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLiftsPcs (
  hookOk_memcpyPcsBudget_of_master hookOk_memcpyPcs_of_master
  hookOk_memcpyRecvPcsS_of_master hookOk_memcpyRecvPcs_of_master
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  hookMemset_masterMemset_ok hookOk_cliMemset_of_master hookOk_libcMemset_of_master
  hookOk_memsetRegion_of_master hookOk_session2MemsetExtern_of_master
  hookOk_sessionMemsetRegion_of_master hookOk_sessionMemset_of_master masterMemsetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  memsetGhostHook memsetGhostHook_master_ok memsetGhostHook_vmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd (
  pksmSlotSpecPlacedOkFs tryFromPlacedSpecOkFs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd (
  stripCodec_keepsFrozen
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferCoreFd (
  MemcpyStripKeepsFrozen memcpyStripKeepsFrozen_hookMemcpy not_badKf_of_memcpy
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferPlacedBudgetFd (
  pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_mc
  tryFrom_okFs_mallocng_cli_placed_at_579_mc
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (
  PksmTryFromEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget (
  subsetA4PksmTryFromPlaced_of_codecHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget (
  SubsetA4PksmTryFromPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  allocContractsFsPlaced_of_hookSat allocContractsXCliPlaced_of_hookSat
  cliExternsPlaced_memmove_budget_sat cliExternsPlaced_sessionMemmove_budget_sat
  codecHooksPlaced_of_hookSat publicApiDecHooksPlaced_of_hookSat stage2ContractsMinPlaced_of_hookSat
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsFsPlaced AllocContractsXCliPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec
  sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget (memcpyPcsBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)

/-! ## 1. `MemcpyStripKeepsFrozen` Ghost Bridges (`linkedCallHook`, `memcpyGhostHook`, `memcpyGhostHookK`) -/

/-- Any `linkedCallHook` with fallback `ProofLib.hookMemcpy` satisfies `MemcpyStripKeepsFrozen`:
on active real runs `ExecFrozen u.mem` transports `KeepsFrozen` across `stripCodecMem`, on
non-`ActiveRealRun` calls `keepFsTrace hookMemcpy` has the same memory as `hookMemcpy`, and outside
`ActiveRealPre` memory is unchanged. -/
theorem memcpyStripKeepsFrozen_linkedCallHook {α : Type}
    (keep_g : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) :
    MemcpyStripKeepsFrozen
      (linkedCallHook keep_g P_real P_sub entryTarget spec ProofLib.hookMemcpy) := by
  intro keep u hact hkf
  classical
  by_cases hPre : ActiveRealPre spec u
  · by_cases hReal : ActiveRealRun keep_g P_real P_sub entryTarget u
    · simp only [linkedCallHook, hPre, hReal, ↓reduceDIte] at hkf ⊢
      exact stripCodec_keepsFrozen keep
        (fun a p hp hx => by have hfr := hReal.1 a; rw [hp] at hfr; exact (hfr hx).2) hkf
    · simp only [linkedCallHook, hPre, hReal, ↓reduceDIte]
      have hmem : (keepFsTrace ProofLib.hookMemcpy u).mem = (ProofLib.hookMemcpy u).mem := rfl
      rw [hmem]
      exact not_badKf_of_memcpy keep hact
  · simp only [linkedCallHook, hPre, ↓reduceDIte]
    exact fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- `MemcpyStripKeepsFrozen` for plain `memcpyGhostHook`. -/
theorem memcpyStripKeepsFrozen_memcpyGhostHook
    (keep_g : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    MemcpyStripKeepsFrozen (memcpyGhostHook keep_g P_real P_sub entryTarget) :=
  memcpyStripKeepsFrozen_linkedCallHook keep_g P_real P_sub entryTarget masterMemcpySpec

/-- `MemcpyStripKeepsFrozen` for `K`-narrowed `memcpyGhostHookK`. -/
theorem memcpyStripKeepsFrozen_memcpyGhostHookK
    (keep_g : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    MemcpyStripKeepsFrozen (memcpyGhostHookK keep_g P_real P_sub entryTarget) :=
  memcpyStripKeepsFrozen_linkedCallHook keep_g P_real P_sub entryTarget
    (memcpySpecK keep_g masterMemcpySpec)

/-! ## 2. `GhostMemcpyRow`, `GhostMemsetRow`, & `BaseHelperRowsSat` (`memmove_eq` Preserved) -/

/-- Contract-level `memcpy` row bundle on an extern map `ext`, bundling `masterMemcpySpec`,
`VmPreserved`, `State.fs` preservation, `HookFsTraced IsFsC`, `MemcpyStripKeepsFrozen`, and
`State.oracle` preservation. -/
@[expose] def GhostMemcpyRow (ext : LibsignalHooks) : Prop :=
  ∃ f : State → State,
    ext memcpyName = some f ∧
    HookOk f masterMemcpySpec ∧
    (∀ s, VmPreserved s (f s)) ∧
    (∀ s, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f ∧
    MemcpyStripKeepsFrozen f ∧
    (∀ s, (f s).oracle = s.oracle)

/-- Contract-level `memset` row bundle on an extern map `ext`, bundling `masterMemsetSpec`,
`VmPreserved`, `State.fs` preservation, and `HookFsTraced IsFsC`. -/
@[expose] def GhostMemsetRow (ext : LibsignalHooks) : Prop :=
  ∃ f : State → State,
    ext memsetName = some f ∧
    HookOk f masterMemsetSpec ∧
    (∀ s, VmPreserved s (f s)) ∧
    (∀ s, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f

/-- Ghost-compatible `BaseHelperRows` counterpart: replaces `memcpy_eq` and `memset_eq` with
`GhostMemcpyRow` and `GhostMemsetRow` while keeping `memmove_eq`, `bcmp_eq`, `utf8_eq`,
`memrchr_eq`, and `panics` unchanged. -/
structure BaseHelperRowsSat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (baseExt : LibsignalHooks) : Prop where
  memcpy_sat : GhostMemcpyRow baseExt
  memset_sat : GhostMemsetRow baseExt
  memmove_eq : baseExt memmoveName = cliExternsPlaced mmpl W memmoveName
  bcmp_eq : baseExt "bcmp" = cliExternsPlaced mmpl W "bcmp"
  utf8_eq : baseExt lsFromUtf8Sym = cliExternsPlaced mmpl W lsFromUtf8Sym
  memrchr_eq : baseExt lsMemrchrSym = cliExternsPlaced mmpl W lsMemrchrSym
  panics : CliPanicHooksPlaced baseExt

/-- Stock `hookMemcpy` satisfies `GhostMemcpyRow`. -/
theorem ghostMemcpyRow_of_hookMemcpy {ext : LibsignalHooks}
    (hrow : ext memcpyName = some hookMemcpy) :
    GhostMemcpyRow ext :=
  ⟨hookMemcpy, hrow, hookMemcpy_masterMemcpy_ok, hookMemcpy_vmPreserved,
    hookMemcpy_fs, hookMemcpy_fsT, memcpyStripKeepsFrozen_hookMemcpy, fun _ => rfl⟩

/-- Stock `hookMemset` satisfies `GhostMemsetRow`. -/
theorem ghostMemsetRow_of_hookMemset {ext : LibsignalHooks}
    (hrow : ext memsetName = some hookMemset) :
    GhostMemsetRow ext :=
  ⟨hookMemset, hrow, hookMemset_masterMemset_ok, hookMemset_vmPreserved,
    hookMemset_fs, hookMemset_fsT⟩

/-- Any `memcpyGhostHook keep P_real P_sub entryTarget` row satisfies `GhostMemcpyRow`. -/
theorem ghostMemcpyRow_of_memcpyGhostHook {ext : LibsignalHooks}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hrow : ext memcpyName = some (memcpyGhostHook keep P_real P_sub entryTarget))
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords) :
    GhostMemcpyRow ext :=
  ⟨memcpyGhostHook keep P_real P_sub entryTarget, hrow,
    memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords,
    memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords,
    linkedCallHook_fs keep P_real P_sub entryTarget masterMemcpySpec hookMemcpy,
    linkedCallHook_fsT keep P_real P_sub entryTarget masterMemcpySpec hookMemcpy,
    memcpyStripKeepsFrozen_memcpyGhostHook keep P_real P_sub entryTarget,
    memcpyGhostHook_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords⟩

/-- Any `memsetGhostHook keep P_real P_sub entryTarget` row satisfies `GhostMemsetRow`. -/
theorem ghostMemsetRow_of_memsetGhostHook {ext : LibsignalHooks}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hrow : ext memsetName = some (memsetGhostHook keep P_real P_sub entryTarget))
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym) :
    GhostMemsetRow ext :=
  ⟨memsetGhostHook keep P_real P_sub entryTarget, hrow,
    memsetGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords,
    memsetGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords,
    linkedCallHook_fs keep P_real P_sub entryTarget masterMemsetSpec hookMemset,
    linkedCallHook_fsT keep P_real P_sub entryTarget masterMemsetSpec hookMemset⟩

/-- Combine `GhostMemcpyRow`, `GhostMemsetRow`, and a `37`-row `BaseHelperRows` witness into
`BaseHelperRowsSat`. -/
theorem BaseHelperRows.toSat {mmpl : Obj.MultiPlacement} {W : CliHooks}
    {baseExt : LibsignalHooks}
    (hMc : GhostMemcpyRow baseExt) (hMs : GhostMemsetRow baseExt)
    (hBase : BaseHelperRows mmpl W baseExt) :
    BaseHelperRowsSat mmpl W baseExt where
  memcpy_sat := hMc
  memset_sat := hMs
  memmove_eq := hBase.memmove_eq
  bcmp_eq := hBase.bcmp_eq
  utf8_eq := hBase.utf8_eq
  memrchr_eq := hBase.memrchr_eq
  panics := hBase.panics

/-- On the `37`-row `cliExternsPlaced mmpl W` (`cliExternsPlaced_memcpy_none`), `cliGhostExterns g`
resolves `memcpyName` strictly to `g.memcpy`. -/
theorem cliGhostExterns_memcpy_placed (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (g : CliGhostHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) memcpyName = g.memcpy := by
  cases hg : g.memcpy with
  | none =>
    exact (cliGhostExterns_memcpy_none g (cliExternsPlaced mmpl W) hg).trans
      (cliExternsPlaced_memcpy_none mmpl W)
  | some f =>
    exact cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hg

/-- On the `37`-row `cliExternsPlaced mmpl W` (`cliExternsPlaced_memset_none`), `cliGhostExterns g`
resolves `memsetName` strictly to `g.memset`. -/
theorem cliGhostExterns_memset_placed (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (g : CliGhostHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) memsetName = g.memset := by
  cases hg : g.memset with
  | none =>
    exact (cliGhostExterns_memset_none g (cliExternsPlaced mmpl W) hg).trans
      (cliExternsPlaced_memset_none mmpl W)
  | some f =>
    exact cliGhostExterns_memset_some g (cliExternsPlaced mmpl W) hg

/-- Canonical `37`-row `BaseHelperRowsSat` witness for `cliGhostExterns g (cliExternsPlaced mmpl W)`
given `GhostMemcpyRow` and `GhostMemsetRow` on the overlaid extern map. -/
theorem cliExternsPlaced_baseHelperRowsSat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (g : CliGhostHooks)
    (hMc : GhostMemcpyRow (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hMs : GhostMemsetRow (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    BaseHelperRowsSat mmpl W (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  memcpy_sat := hMc
  memset_sat := hMs
  memmove_eq := cliGhostExterns_other g (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  bcmp_eq := cliGhostExterns_other g (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  utf8_eq := cliGhostExterns_other g (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  memrchr_eq := cliGhostExterns_other g (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  panics := cliGhostExterns_panics g
    (LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.cliExternsPlaced_baseHelperRows
      mmpl W).panics

theorem GhostMemcpyRow.of_eq {ext₁ ext₂ : LibsignalHooks}
    (heq : ext₂ memcpyName = ext₁ memcpyName) (h : GhostMemcpyRow ext₁) :
    GhostMemcpyRow ext₂ := by
  rcases h with ⟨f, hrow, hok, hvm, hfs, hfst, hskf, horc⟩
  exact ⟨f, heq.trans hrow, hok, hvm, hfs, hfst, hskf, horc⟩

theorem GhostMemsetRow.of_eq {ext₁ ext₂ : LibsignalHooks}
    (heq : ext₂ memsetName = ext₁ memsetName) (h : GhostMemsetRow ext₁) :
    GhostMemsetRow ext₂ := by
  rcases h with ⟨f, hrow, hok, hvm, hfs, hfst⟩
  exact ⟨f, heq.trans hrow, hok, hvm, hfs, hfst⟩

/-- `none`-slot pass-through only (`g.memcpy = none`); not usable on the K or Narrow routes. -/
theorem GhostMemcpyRow.cliGhostExterns {baseExt : LibsignalHooks} (g : CliGhostHooks)
    (hNone : g.memcpy = none) (h : GhostMemcpyRow baseExt) :
    GhostMemcpyRow (cliGhostExterns g baseExt) :=
  h.of_eq (cliGhostExterns_memcpy_none g baseExt hNone)

/-- `none`-slot pass-through only (`g.memset = none`); not usable on the K or Narrow routes. -/
theorem GhostMemsetRow.cliGhostExterns {baseExt : LibsignalHooks} (g : CliGhostHooks)
    (hNone : g.memset = none) (h : GhostMemsetRow baseExt) :
    GhostMemsetRow (cliGhostExterns g baseExt) :=
  h.of_eq (cliGhostExterns_memset_none g baseExt hNone)

theorem cliGhostExterns_memmove_eq_of_sat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {baseExt : LibsignalHooks} (g : CliGhostHooks) (hBase : BaseHelperRowsSat mmpl W baseExt) :
    cliGhostExterns g baseExt memmoveName = cliExternsPlaced mmpl W memmoveName :=
  (cliGhostExterns_other g baseExt (sym := memmoveName)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hBase.memmove_eq

/-- `none`-slot pass-through only (`g.memcpy = none`, `g.memset = none`); not usable on the K or Narrow routes. -/
theorem BaseHelperRowsSat.cliGhostExterns {mmpl : Obj.MultiPlacement} {W : CliHooks}
    {baseExt : LibsignalHooks} (g : CliGhostHooks)
    (hMcNone : g.memcpy = none) (hMsNone : g.memset = none)
    (hBase : BaseHelperRowsSat mmpl W baseExt) :
    BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt) where
  memcpy_sat := hBase.memcpy_sat.cliGhostExterns g hMcNone
  memset_sat := hBase.memset_sat.cliGhostExterns g hMsNone
  memmove_eq := cliGhostExterns_memmove_eq_of_sat mmpl W g hBase
  bcmp_eq := (cliGhostExterns_other g baseExt (sym := "bcmp")
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hBase.bcmp_eq
  utf8_eq := (cliGhostExterns_other g baseExt (sym := lsFromUtf8Sym)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hBase.utf8_eq
  memrchr_eq := (cliGhostExterns_other g baseExt (sym := lsMemrchrSym)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hBase.memrchr_eq
  panics := cliGhostExterns_panics g hBase.panics

/-! ## 3. Generic & Contract-Specific `HookSat` Dischargers (`GhostMemcpyRow` & `GhostMemsetRow`) -/

theorem GhostMemcpyRow.hookSat_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemcpyRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemcpySpec → HookOk f spec) :
    HookSat ext memcpyName spec := by
  rcases h with ⟨f, hrow, hok, _, _, _, _, _⟩
  exact ⟨f, hrow, hlift hok⟩

theorem GhostMemcpyRow.hookSat_keepsFs_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemcpyRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemcpySpec → HookOk f spec) :
    HookSat ext memcpyName spec.keepsFs := by
  rcases h with ⟨f, hrow, hok, _, hfs, _, _, _⟩
  exact ⟨f, hrow, (hlift hok).keepsFs hfs⟩

theorem GhostMemcpyRow.hookSat_budget_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemcpyRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemcpySpec → HookOk f spec) :
    HookSat ext memcpyName (withVmPreserved spec) := by
  rcases h with ⟨f, hrow, hok, hvm, _, _, _, _⟩
  exact ⟨f, hrow, hookOk_withVmPreserved (hlift hok) hvm⟩

theorem GhostMemcpyRow.hookSat_budget_keepsFs_of_master {α : Type} {ext : LibsignalHooks}
    {spec : Spec α} (h : GhostMemcpyRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemcpySpec → HookOk f spec) :
    HookSat ext memcpyName (withVmPreserved spec).keepsFs := by
  rcases h with ⟨f, hrow, hok, hvm, hfs, _, _, _⟩
  exact ⟨f, hrow, (hookOk_withVmPreserved (hlift hok) hvm).keepsFs hfs⟩

theorem GhostMemsetRow.hookSat_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemsetRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemsetSpec → HookOk f spec) :
    HookSat ext memsetName spec := by
  rcases h with ⟨f, hrow, hok, _, _, _⟩
  exact ⟨f, hrow, hlift hok⟩

theorem GhostMemsetRow.hookSat_keepsFs_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemsetRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemsetSpec → HookOk f spec) :
    HookSat ext memsetName spec.keepsFs := by
  rcases h with ⟨f, hrow, hok, _, hfs, _⟩
  exact ⟨f, hrow, (hlift hok).keepsFs hfs⟩

theorem GhostMemsetRow.hookSat_budget_of_master {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (h : GhostMemsetRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemsetSpec → HookOk f spec) :
    HookSat ext memsetName (withVmPreserved spec) := by
  rcases h with ⟨f, hrow, hok, hvm, _, _⟩
  exact ⟨f, hrow, hookOk_withVmPreserved (hlift hok) hvm⟩

theorem GhostMemsetRow.hookSat_budget_keepsFs_of_master {α : Type} {ext : LibsignalHooks}
    {spec : Spec α} (h : GhostMemsetRow ext)
    (hlift : ∀ {f : State → State}, HookOk f masterMemsetSpec → HookOk f spec) :
    HookSat ext memsetName (withVmPreserved spec).keepsFs := by
  rcases h with ⟨f, hrow, hok, hvm, hfs, _⟩
  exact ⟨f, hrow, (hookOk_withVmPreserved (hlift hok) hvm).keepsFs hfs⟩

-- 3.1 Shared CLI / Stage2 / Codec `memcpy` `HookSat` dischargers:

theorem GhostMemcpyRow.libcMemcpy_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext)
    (stk : Nat := 4096) :
    HookSat ext memcpyName (libcMemcpySpec stk) :=
  h.hookSat_of_master fun hh => hookOk_libcMemcpy_of_master hh stk

theorem GhostMemcpyRow.libcMemcpy_keepsFs_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext)
    (stk : Nat := 4096) :
    HookSat ext memcpyName (libcMemcpySpec stk).keepsFs :=
  h.hookSat_keepsFs_of_master fun hh => hookOk_libcMemcpy_of_master hh stk

theorem GhostMemcpyRow.libcMemcpy_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext)
    (stk : Nat := 4096) :
    HookSat ext memcpyName (withVmPreserved (libcMemcpySpec stk)) :=
  h.hookSat_budget_of_master fun hh => hookOk_libcMemcpy_of_master hh stk

theorem GhostMemcpyRow.sessionMemcpy_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext)
    (stk : Nat := 4096) :
    HookSat ext memcpyName (sessionMemcpySpec stk) :=
  h.hookSat_of_master fun hh => hookOk_sessionMemcpy_of_master hh stk

theorem GhostMemcpyRow.sessionMemcpy_keepsFs_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext)
    (stk : Nat := 4096) :
    HookSat ext memcpyName (sessionMemcpySpec stk).keepsFs :=
  h.hookSat_keepsFs_of_master fun hh => hookOk_sessionMemcpy_of_master hh stk

theorem GhostMemcpyRow.sessionMemcpy_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext)
    (stk : Nat := 4096) :
    HookSat ext memcpyName (sessionMemcpyBudgetSpec stk) :=
  h.hookSat_budget_of_master fun hh => hookOk_sessionMemcpy_of_master hh stk

theorem GhostMemcpyRow.cliMemcpy_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName memcpySpec :=
  h.hookSat_of_master hookOk_cliMemcpy_of_master

theorem GhostMemcpyRow.cliMemcpy_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName (withVmPreserved memcpySpec) :=
  h.hookSat_budget_of_master hookOk_cliMemcpy_of_master

theorem GhostMemcpyRow.memcpyRegion_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName memcpyRegionSpec :=
  h.hookSat_of_master hookOk_memcpyRegion_of_master

theorem GhostMemcpyRow.memcpyRegion_keepsFs_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName memcpyRegionSpec.keepsFs :=
  h.hookSat_keepsFs_of_master hookOk_memcpyRegion_of_master

theorem GhostMemcpyRow.memcpyRegion_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName (withVmPreserved memcpyRegionSpec) :=
  h.hookSat_budget_of_master hookOk_memcpyRegion_of_master

theorem GhostMemcpyRow.sessionMemcpyRegion_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName sessionMemcpyRegionSpec :=
  h.hookSat_of_master hookOk_sessionMemcpyRegion_of_master

theorem GhostMemcpyRow.sessionMemcpyRegion_keepsFs_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName sessionMemcpyRegionSpec.keepsFs :=
  h.hookSat_keepsFs_of_master hookOk_sessionMemcpyRegion_of_master

theorem GhostMemcpyRow.sessionMemcpyRegion_withStack_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) (stk : Nat := 4096) :
    HookSat ext memcpyName (withStack sessionMemcpyRegionSpec stk) :=
  h.hookSat_of_master fun hh => hookOk_withStack (hookOk_sessionMemcpyRegion_of_master hh) stk

theorem GhostMemcpyRow.sessionMemcpyRegion_budget_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName sessionMemcpyRegionBudgetSpec :=
  h.hookSat_budget_of_master hookOk_sessionMemcpyRegion_of_master

theorem GhostMemcpyRow.framelessMemcpy_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName framelessMemcpySpec :=
  h.hookSat_of_master hookOk_framelessMemcpy_of_master

theorem GhostMemcpyRow.framelessMemcpy_keepsFs_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName framelessMemcpySpec.keepsFs :=
  h.hookSat_keepsFs_of_master hookOk_framelessMemcpy_of_master

theorem GhostMemcpyRow.framelessMemcpy_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName framelessMemcpyBudgetSpec :=
  h.hookSat_budget_of_master hookOk_framelessMemcpy_of_master

theorem GhostMemcpyRow.sessionMemcpyRegionRO_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
  h.hookSat_of_master hookOk_sessionMemcpyRegionRO_of_master

theorem GhostMemcpyRow.sessionMemcpyRegionRO_budget_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName
      (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) :=
  h.hookSat_budget_of_master hookOk_sessionMemcpyRegionRO_of_master

theorem GhostMemcpyRow.memcpyROExt_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext)
    (stk : Nat := 16384) :
    HookSat ext memcpyName (memcpyROExtSpec stk) :=
  h.hookSat_of_master fun hh => hookOk_memcpyROExt_of_master hh stk

theorem GhostMemcpyRow.memcpyROExt_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext)
    (stk : Nat := 16384) :
    HookSat ext memcpyName (withVmPreserved (memcpyROExtSpec stk)) :=
  h.hookSat_budget_of_master fun hh => hookOk_memcpyROExt_of_master hh stk

theorem GhostMemcpyRow.cliMemcpyRO_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName memcpyROSpec :=
  h.hookSat_of_master hookOk_cliMemcpyRO_of_master

theorem GhostMemcpyRow.cliMemcpyRO_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName (withVmPreserved memcpyROSpec) :=
  h.hookSat_budget_of_master hookOk_cliMemcpyRO_of_master

theorem GhostMemcpyRow.sessionMemcpyRO4K_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K :=
  h.hookSat_of_master hookOk_sessionMemcpyRO4K_of_master

theorem GhostMemcpyRow.sessionMemcpyRO4K_budget_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName
      (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K) :=
  h.hookSat_budget_of_master hookOk_sessionMemcpyRO4K_of_master

theorem GhostMemcpyRow.allocMemcpyVm_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName allocMemcpyVmSpec := by
  rcases h with ⟨f, hrow, hok, hvm, _, _, _, horc⟩
  exact ⟨f, hrow, hookOk_allocMemcpyVm_of_master hok hvm horc⟩

-- 3.2 `WP6a-mc1` (`MemcpyGhostLifts` & `MemcpyGhostLiftsPcs`) file-local `HookSat` dischargers:

theorem GhostMemcpyRow.openMemcpy_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName openMemcpySpec :=
  h.hookSat_of_master hookOk_openMemcpy_of_master

theorem GhostMemcpyRow.openMemcpy_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName (withVmPreserved openMemcpySpec) :=
  h.hookSat_budget_of_master hookOk_openMemcpy_of_master

theorem GhostMemcpyRow.openMemcpyRo_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName openMemcpyRoSpec :=
  h.hookSat_of_master hookOk_openMemcpyRo_of_master

theorem GhostMemcpyRow.openMemcpyRo_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName (withVmPreserved openMemcpyRoSpec) :=
  h.hookSat_budget_of_master hookOk_openMemcpyRo_of_master

theorem GhostMemcpyRow.hashbrownMemcpyRegion_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName hashbrownMemcpyRegionSpec :=
  h.hookSat_of_master hookOk_hashbrownMemcpyRegion_of_master

theorem GhostMemcpyRow.hashbrownMemcpyRegion_budget_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName (withVmPreserved hashbrownMemcpyRegionSpec) :=
  h.hookSat_budget_of_master hookOk_hashbrownMemcpyRegion_of_master

theorem GhostMemcpyRow.pqxdhMemcpyRegion_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName pqxdhMemcpyRegionSpec :=
  h.hookSat_of_master hookOk_pqxdhMemcpyRegion_of_master

theorem GhostMemcpyRow.pqxdhMemcpyRegion_budget_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName (withVmPreserved pqxdhMemcpyRegionSpec) :=
  h.hookSat_budget_of_master hookOk_pqxdhMemcpyRegion_of_master

theorem GhostMemcpyRow.chainClone3SessionMemcpy_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec :=
  h.hookSat_of_master hookOk_chainClone3SessionMemcpy_of_master

theorem GhostMemcpyRow.chainClone3SessionMemcpyBudget_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName
      LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget.sessionMemcpySpec := by
  rcases h with ⟨f, hrow, hok, hvm, _, _, _, _⟩
  exact ⟨f, hrow, hookOk_chainClone3SessionMemcpyBudget_of_master hok hvm⟩

theorem GhostMemcpyRow.recordSessionCloneMemcpy_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName
      CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec :=
  h.hookSat_of_master hookOk_recordSessionCloneMemcpy_of_master

theorem GhostMemcpyRow.recordSessionCloneMemcpy_budget_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName
      (withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec) :=
  h.hookSat_budget_of_master hookOk_recordSessionCloneMemcpy_of_master

theorem GhostMemcpyRow.rustStdAllocMemcpyVm_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec := by
  rcases h with ⟨f, hrow, hok, hvm, _, _, _, horc⟩
  exact ⟨f, hrow, hookOk_rustStdAllocMemcpyVm_of_master hok hvm horc⟩

theorem GhostMemcpyRow.sessionMemcpyROX_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName sessionMemcpyROXSpec :=
  h.hookSat_of_master hookOk_sessionMemcpyROX_of_master

theorem GhostMemcpyRow.sessionMemcpyROX_budget_sat {ext : LibsignalHooks}
    (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName (withVmPreserved sessionMemcpyROXSpec) :=
  h.hookSat_budget_of_master hookOk_sessionMemcpyROX_of_master

theorem GhostMemcpyRow.memcpyRecvPcs_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName memcpyRecvPcsSpec :=
  h.hookSat_of_master hookOk_memcpyRecvPcs_of_master

theorem GhostMemcpyRow.memcpyRecvPcsS_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName memcpyRecvPcsSpecS :=
  h.hookSat_of_master hookOk_memcpyRecvPcsS_of_master

theorem GhostMemcpyRow.memcpyRecvPcs_budget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName (withVmPreserved memcpyRecvPcsSpec) :=
  h.hookSat_budget_of_master hookOk_memcpyRecvPcs_of_master

theorem GhostMemcpyRow.memcpyPcs_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName memcpyPcsSpec :=
  h.hookSat_of_master hookOk_memcpyPcs_of_master

theorem GhostMemcpyRow.memcpyPcsBudget_sat {ext : LibsignalHooks} (h : GhostMemcpyRow ext) :
    HookSat ext memcpyName memcpyPcsBudgetSpec := by
  rcases h with ⟨f, hrow, hok, hvm, _, _, _, _⟩
  exact ⟨f, hrow, hookOk_memcpyPcsBudget_of_master hok hvm⟩

-- 3.3 Shared CLI `memset` `HookSat` dischargers:

theorem GhostMemsetRow.libcMemset_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext)
    (stk : Nat := 4096) :
    HookSat ext memsetName (libcMemsetSpec stk) :=
  h.hookSat_of_master fun hh => hookOk_libcMemset_of_master hh stk

theorem GhostMemsetRow.libcMemset_keepsFs_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext)
    (stk : Nat := 4096) :
    HookSat ext memsetName (libcMemsetSpec stk).keepsFs :=
  h.hookSat_keepsFs_of_master fun hh => hookOk_libcMemset_of_master hh stk

theorem GhostMemsetRow.libcMemset_budget_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext)
    (stk : Nat := 4096) :
    HookSat ext memsetName (withVmPreserved (libcMemsetSpec stk)) :=
  h.hookSat_budget_of_master fun hh => hookOk_libcMemset_of_master hh stk

theorem GhostMemsetRow.sessionMemset_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext)
    (stk : Nat := 4096) :
    HookSat ext memsetName (sessionMemsetSpec stk) :=
  h.hookSat_of_master fun hh => hookOk_sessionMemset_of_master hh stk

theorem GhostMemsetRow.sessionMemset_keepsFs_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext)
    (stk : Nat := 4096) :
    HookSat ext memsetName (sessionMemsetSpec stk).keepsFs :=
  h.hookSat_keepsFs_of_master fun hh => hookOk_sessionMemset_of_master hh stk

theorem GhostMemsetRow.sessionMemset_budget_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext)
    (stk : Nat := 4096) :
    HookSat ext memsetName (sessionMemsetBudgetSpec stk) :=
  h.hookSat_budget_of_master fun hh => hookOk_sessionMemset_of_master hh stk

theorem GhostMemsetRow.cliMemset_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext) :
    HookSat ext memsetName memsetSpec :=
  h.hookSat_of_master hookOk_cliMemset_of_master

theorem GhostMemsetRow.cliMemset_budget_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext) :
    HookSat ext memsetName (withVmPreserved memsetSpec) :=
  h.hookSat_budget_of_master hookOk_cliMemset_of_master

theorem GhostMemsetRow.memsetRegion_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext) :
    HookSat ext memsetName memsetRegionSpec :=
  h.hookSat_of_master hookOk_memsetRegion_of_master

theorem GhostMemsetRow.memsetRegion_budget_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext) :
    HookSat ext memsetName (withVmPreserved memsetRegionSpec) :=
  h.hookSat_budget_of_master hookOk_memsetRegion_of_master

theorem GhostMemsetRow.sessionMemsetRegion_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext) :
    HookSat ext memsetName sessionMemsetRegionSpec :=
  h.hookSat_of_master hookOk_sessionMemsetRegion_of_master

theorem GhostMemsetRow.sessionMemsetRegion_budget_sat {ext : LibsignalHooks}
    (h : GhostMemsetRow ext) :
    HookSat ext memsetName sessionMemsetRegionBudgetSpec :=
  h.hookSat_budget_of_master hookOk_sessionMemsetRegion_of_master

theorem GhostMemsetRow.session2MemsetExtern_sat {ext : LibsignalHooks} (h : GhostMemsetRow ext)
    (stk : Nat := 16384) :
    HookSat ext memsetName (session2MemsetExternSpec stk) :=
  h.hookSat_of_master fun hh => hookOk_session2MemsetExtern_of_master hh stk

theorem GhostMemsetRow.session2MemsetExtern_budget_sat {ext : LibsignalHooks}
    (h : GhostMemsetRow ext) (stk : Nat := 16384) :
    HookSat ext memsetName (withVmPreserved (session2MemsetExternSpec stk)) :=
  h.hookSat_budget_of_master fun hh => hookOk_session2MemsetExtern_of_master hh stk

/-! ## 4. Bundle & Pure-`fs` Codec Adapter Theorems over `BaseHelperRowsSat` -/

theorem allocContractsXCliPlaced_of_ghost_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (hBase : BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt))
    (hG : CliGhostAllocHooks M A lim g) :
    AllocContractsXCliPlaced A lim (cliGhostExterns g baseExt) := by
  have hMc := hBase.memcpy_sat
  have hMs := hBase.memset_sat
  exact allocContractsXCliPlaced_of_hookSat
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    ⟨g.realloc, cliGhostExterns_realloc g baseExt, hG.realloc⟩
    (shim_budget_sat_of_eq baseExt hG.shim_eq)
    (fun stk => hMc.libcMemcpy_budget_sat stk)
    (fun stk => hMc.sessionMemcpy_budget_sat stk)
    hMc.memcpyRegion_budget_sat
    hMc.sessionMemcpyRegion_budget_sat
    (fun stk => hookSat_of_eq hBase.memmove_eq
      (cliExternsPlaced_memmove_budget_sat mmpl W stk))
    (fun stk => hookSat_of_eq hBase.memmove_eq
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W stk))
    (fun stk _ => hMs.libcMemset_budget_sat stk)
    (fun stk _ => hMs.sessionMemset_budget_sat stk)
    hMs.memsetRegion_budget_sat
    hMs.sessionMemsetRegion_budget_sat

theorem allocContractsFsPlaced_of_ghost_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (hBase : BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt))
    (hG : CliGhostAllocHooks M A lim g) :
    AllocContractsFsPlaced A lim (cliGhostExterns g baseExt) := by
  have hMc := hBase.memcpy_sat
  have hMs := hBase.memset_sat
  refine allocContractsFsPlaced_of_hookSat
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    ⟨g.realloc, cliGhostExterns_realloc g baseExt, hG.realloc⟩
    (shim_budget_sat_of_eq baseExt hG.shim_eq)
    (fun stk => hMc.libcMemcpy_budget_sat stk)
    (fun stk => hMc.sessionMemcpy_budget_sat stk)
    hMc.memcpyRegion_budget_sat
    hMc.sessionMemcpyRegion_budget_sat
    hMc.sessionMemcpyRegionRO_budget_sat
    (fun stk => hookSat_of_eq hBase.memmove_eq
      (cliExternsPlaced_memmove_budget_sat mmpl W stk))
    (fun stk => hookSat_of_eq hBase.memmove_eq
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W stk))
    (fun stk _ => hMs.libcMemset_budget_sat stk)
    (fun stk _ => hMs.sessionMemset_budget_sat stk)
    hMs.memsetRegion_budget_sat
    hMs.sessionMemsetRegion_budget_sat
    ?_
  intro sym hmem f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [cliGhostExterns_alloc] at hf; cases hf; exact hG.alloc_fs
  · rw [cliGhostExterns_dealloc] at hf; cases hf; exact hG.dealloc_fs
  · rw [cliGhostExterns_realloc] at hf; cases hf; exact hG.realloc_fs
  · rw [cliGhostExterns_shim, hG.shim_eq] at hf; cases hf; exact hookNoop_fs
  · rcases hMc with ⟨f_mc, hrow_mc, _, _, hfs_mc, _, _, _⟩
    rw [hrow_mc] at hf; cases hf; exact hfs_mc
  · rw [hBase.memmove_eq,
        cliExternsPlaced_row mmpl W (memmove_row_placed mmpl W)] at hf
    cases hf; exact hookMemmove_fs
  · rcases hMs with ⟨f_ms, hrow_ms, _, _, hfs_ms, _⟩
    rw [hrow_ms] at hf; cases hf; exact hfs_ms

theorem stage2ContractsMinPlaced_of_ghost_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (hBase : BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt))
    (hG : CliGhostAllocHooks M A lim g) :
    Stage2ContractsMinPlaced M A lim (cliGhostExterns g baseExt) :=
  stage2ContractsMinPlaced_of_hookSat
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    ⟨g.realloc, cliGhostExterns_realloc g baseExt, hG.realloc⟩
    (shim_budget_sat_of_eq baseExt hG.shim_eq)
    (hBase.memcpy_sat.sessionMemcpy_budget_sat extHookStack)
    (hookSat_of_eq hBase.memmove_eq
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W extHookStack))

theorem codecHooksPlaced_of_ghost_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (hBase : BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt))
    (hG : CliGhostAllocHooks M A lim g) :
    CodecHooksPlaced M A lim (cliGhostExterns g baseExt) :=
  codecHooksPlaced_of_hookSat
    (noAllocShim_budget_sat_of_eq baseExt hG.shim_eq)
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.realloc, cliGhostExterns_realloc g baseExt, hG.realloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    hBase.memcpy_sat.framelessMemcpy_budget_sat
    (hBase.panics lsHandleAllocErrorSym (by decide))
    (hBase.panics lsHandleErrorSym (by decide))

theorem publicApiDecHooksPlaced_of_ghost_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (hBase : BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt))
    (hG : CliGhostAllocHooks M A lim g)
    (hStrClone : HookSat (cliGhostExterns g baseExt) lsStringCloneSym
      (stringCloneBudgetSpec M A lim)) :
    PublicApiDecHooksPlaced A lim (cliGhostExterns g baseExt) :=
  publicApiDecHooksPlaced_of_hookSat
    (shim_budget_sat_of_eq baseExt hG.shim_eq)
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    hBase.memcpy_sat.sessionMemcpyRegion_budget_sat
    hStrClone
    (hBase.panics lsHandleErrorSym (by decide))
    (hBase.panics lsExpectFailedSym (by decide))

/-- Pure-`fs` `tryFrom` (`Block 85`) at `lsProg_579` discharged from `BaseHelperRowsSat`. -/
theorem tryFrom_okFs_mallocng_cli_placed_at_579_of_sat [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks) (baseExt : LibsignalHooks)
    (hBase : BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt))
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g) :
    subroutine_ok (lsProg_579 (cliGhostExterns g baseExt)) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpecOkFs (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)) := by
  rcases hBase.memcpy_sat with ⟨f_mc, hrow, hok, hvm, hfs, _, hskf, _⟩
  exact tryFrom_okFs_mallocng_cli_placed_at_579_mc I hS γ mmpl tp brkStart lim g baseExt f_mc
    hG hrow (hookOk_withVmPreserved (hookOk_framelessMemcpy_of_master hok) hvm) hfs hskf
    (hBase.panics lsHandleAllocErrorSym (by decide))
    (hBase.panics lsHandleErrorSym (by decide))

/-- `fineHookRustCliAllocBudget` specialization of `tryFrom_okFs_mallocng_cli_placed_at_579_of_sat`. -/
theorem tryFrom_okFs_fine_cli_placed_at_579_of_sat [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks) (baseExt : LibsignalHooks)
    (hBase : BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt))
    (hG : CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim g) :
    subroutine_ok (lsProg_579 (cliGhostExterns g baseExt)) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpecOkFs (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  tryFrom_okFs_mallocng_cli_placed_at_579_of_sat _ _ γ mmpl tp brkStart lim g W baseExt hBase hG

/-- Pure-`fs` `pksmSlot` (`Block 111`) at `lsProg_579` discharged from `BaseHelperRowsSat`. -/
theorem pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_of_sat [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks) (baseExt : LibsignalHooks)
    {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    (hBase : BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt))
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hSub : ∀ {A' : RustCliAllocBudget M} {H' : LibsignalHooks},
      CodecHooksPlaced M A' lim H' → SubsetA4PksmTryFromPlaced M A' lim PksmEnv H')
    (hParse : ∀ b, S.pksmParse b = pksmParse b) :
    subroutine_ok (lsProg_579 (cliGhostExterns g baseExt)) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S) := by
  rcases hBase.memcpy_sat with ⟨f_mc, hrow, hok, hvm, hfs, _, hskf, _⟩
  exact pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_mc I hS γ mmpl tp brkStart lim g
    baseExt f_mc hG hrow (hookOk_withVmPreserved (hookOk_framelessMemcpy_of_master hok) hvm)
    hfs hskf
    (hBase.panics lsHandleAllocErrorSym (by decide))
    (hBase.panics lsHandleErrorSym (by decide))
    hSub hParse

/-- `fineHookRustCliAllocBudget` specialization of
`pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_of_sat`. -/
theorem pksmSlot_okFs_of_subsetA4_fine_cli_placed_at_579_of_sat [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks) (baseExt : LibsignalHooks)
    {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    (hBase : BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt))
    (hG : CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim g)
    (hSub : ∀ {A' : RustCliAllocBudget fineCostModel} {H' : LibsignalHooks},
      CodecHooksPlaced fineCostModel A' lim H' →
        SubsetA4PksmTryFromPlaced fineCostModel A' lim PksmEnv H')
    (hParse : ∀ b, S.pksmParse b = pksmParse b) :
    subroutine_ok (lsProg_579 (cliGhostExterns g baseExt)) blkPl_111.base
      (pksmSlotSpecPlacedOkFs fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim PksmEnv S) :=
  pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_of_sat _ _ γ mmpl tp brkStart lim g W
    baseExt hBase hG hSub hParse

/-- Ready-to-apply `PksmTryFromEnv` specialization of
`pksmSlot_okFs_of_subsetA4_fine_cli_placed_at_579_of_sat`. -/
theorem pksmSlot_okFs_fine_cli_placed_at_579_of_sat [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks) (baseExt : LibsignalHooks)
    {S : RunSem}
    (hBase : BaseHelperRowsSat mmpl W (cliGhostExterns g baseExt))
    (hG : CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim g)
    (hParse : ∀ b, S.pksmParse b = pksmParse b) :
    subroutine_ok (lsProg_579 (cliGhostExterns g baseExt)) blkPl_111.base
      (pksmSlotSpecPlacedOkFs fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim PksmTryFromEnv S) :=
  pksmSlot_okFs_of_subsetA4_fine_cli_placed_at_579_of_sat γ mmpl tp brkStart lim g W baseExt
    hBase hG (fun hC => subsetA4PksmTryFromPlaced_of_codecHooks hC) hParse

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliMemcpyRowSat
