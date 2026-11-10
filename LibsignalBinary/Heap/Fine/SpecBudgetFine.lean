/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Heap.Fine.AllocZeroedFine
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `SpecBudget` Hook and Entry Bundle Instantiations at `fineCostModel`

Instantiates the budget-threaded hook and compiled-entry bundles of `LibsignalBinary.Heap.SpecBudget`
over `fineCostModel`, providing both `fineHookRustCliAllocBudget` (with read-only `mallocngLib` code
ownership) and raw `fineRustCliAllocBudget` assemblies for `AllocHooksBudget`,
`TripleRatchetHooksBudget`, `PublicApiHooksBudget`, `SpqrHooksBudget`, and `CliExternsBudgetOk`.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Process ProofLib
open ProofLib.StdStartup (hasInstrs)
open CryptoVerification (LibsignalPlacement)
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel aesDecName aesEncName allocZeroedName dhName
  fmtWriteName formatInnerName pubFromSecretName sharedDropName staticDropName
)
open CryptoVerification.LibsignalPublicApi (
  durationSinceHookName isTrustedHookName loadSessionHookName
  saveIdentityHookName storeSessionHookName stringCloneHookName timeAddHookName
)
open CryptoVerification.LibsignalSpqrV1 (
  MlKem
  libcruxHmacName mlkemDecapsName mlkemDecapsSpec mlkemEncaps1Name mlkemEncaps1Spec
  mlkemEncaps2Name mlkemEncaps2Spec mlkemFromSeedName mlkemFromSeedSpec
  mlkemPk1Name mlkemPk1Spec mlkemPk2Name mlkemPk2Spec
  mlkemValidatePkName mlkemValidatePkSpec
)
open CryptoVerification.E2E (
  PEParams PqxdhPrims aesDecHookMallocng aesEncHookMallocng
  compress512Name compressName dsmbName edNegName kemDecapsName kemEncapsName
  libcruxHmacHookMallocng scalarModName scalarWideName toEdwardsName torsionFreeName
)
open CryptoVerification.SignalSession (
  CliHooks
  cliBcmpHook durationSinceExactHook fromUtf8Hook memrchrHook
  readFileName readStdinName strlenHook writeFileHook writeFileName
  writeStdoutHook writeStdoutName
)
open CryptoVerification.SignalSession.CliExt (
  bcmpSpec blackBoxSpec compress256Spec compress512Spec dhSpec dsmbSpec
  fromUtf8Spec ioNames kemDecapsSpec kemEncapsSpec memcpyROSpec memcpySpec
  memmoveSpec memrchrSpec memsetSpec pubFromSecretSpec pureByteFunctionSpec
  shimSpec strlenSpec toEdwardsSpec torsionFreeSpec zeroizeSpec
)
open VerifiedLibraries.Mallocng (
  MallocngAuxvAt MallocngBrkStartWf MallocngRuntime mallocngAddrsOfPlacement
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustAllocAddrs RustCliAllocBudget RustCliAllocBudgetEntriesBase
  RustCliAllocBudgetHooksBase VmPreserved mallocngBudgetPoolInv
  rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  allocMemcpyVmSpec stringCloneBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (
  AllocHooksBudget AllocHooksBudgetBase CliExternsBudgetOk PublicApiHooksBudget
  PublicApiHooksNoSessionStoreBudget PublicApiStoreEnv SpqrHooksBudget
  TripleRatchetHooksBudget aesDecBudgetSpec aesEncBudgetSpec cliAllocNames
  defaultPublicApiStoreEnv durationSinceBudgetSpec durationSinceEpochBudgetSpec
  fmtWriteBudgetSpec formatInnerBudgetSpec hookSat_writeFileBudget_of_hookSat
  hookSat_writeStdoutBudget_of_hookSat isTrustedBudgetSpec libcruxHmacBudgetSpec
  loadSessionBudgetSpec readFileBudgetSpec readStdinBudgetSpec
  rustAllocZeroedBudgetSpec rustAllocZeroedBudgetSpecBase
  saveIdentityBudgetSpec storeSessionBudgetSpec timeAddBudgetSpec
  vmPreserved_writeFileHook vmPreserved_writeStdoutHook withVmPreserved
  writeFileBudgetSpec writeStdoutBudgetSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineAesDec_budget_hookSat fineAesEnc_budget_hookSat
  fineHookBudgetPool_of_init fineHookRdlAllocZeroed_budget_placed_ok
  fineHookRustCliAllocBudget fineHookRustCliAllocBudgetEntries
  fineHookRustCliAllocBudgetEntries_thunks fineHookRustCliAllocZeroedBudget_thunk_ok
  fineLibcruxHmac_budget_hookSat fineStringClone_budget_hookSat
  stringCloneHookMallocng
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  CodeBlocksPermRX mallocngHookBudgetPool_of_codeLoaded
)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng)
open VerifiedLibraries.RustStd (
  RustStdRdlShimCode RustStdThunkCode mallocngPlacedCAddrs
)

export LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineHookRustCliAllocBudget fineHookBudgetPool_of_init
  fineHookRustCliAllocBudgetEntries fineHookRustCliAllocBudgetEntries_thunks
  fineHookRdlAllocZeroed_budget_placed_ok
)
export LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineHookRustCliAllocZeroedBudget_thunk_ok stringCloneHookMallocng
  fineAesEnc_budget_hookSat fineAesDec_budget_hookSat fineLibcruxHmac_budget_hookSat
)
export LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineStringClone_budget_hookSat
)

/-! ## Unified and Raw Fine Budget Pool Bridges -/

/-- `fineHookRustCliAllocBudget` and `fineRustCliAllocBudget` share the exact same underlying
    `RustAlloc` (`repAlloc`), so all heap representation predicates (`vecU8`, `vecGhostAt`,
    `sessionRecordAt`, `protocolAddressAt`, `CliExt.ioVecAt`) coincide definitionally (`rfl`). -/
theorem fineHookRustCliAllocBudget_repAlloc_eq (γ : GhostName)
    (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    (fineHookRustCliAllocBudget γ mpl tp brkStart).repAlloc =
      (fineRustCliAllocBudget γ mpl tp brkStart).repAlloc :=
  rfl

/-- Upgrade `(fineRustCliAllocBudget γ mpl tp brkStart).pool lim st s ∗ R` to
    `(fineHookRustCliAllocBudget γ mpl tp brkStart).pool lim st s ∗ R` whenever
    `VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem` holds. -/
theorem fineHookBudgetPool_of_codeLoaded
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : FineBudget} {s : State} {R : SepProp}
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem)
    (hsat : s.mem ⊨ (fineRustCliAllocBudget γ mpl tp brkStart).pool lim st s ∗ R) :
    s.mem ⊨ (fineHookRustCliAllocBudget γ mpl tp brkStart).pool lim st s ∗ R :=
  mallocngHookBudgetPool_of_codeLoaded (M := fineCostModel) (I := fineCostModelIface) hCL hsat

/-- Entailment-level counterpart of `fineHookBudgetPool_of_codeLoaded` from explicit
    `VerifiedLibraries.mallocngLib.codeRO mpl` and `CodeBlocksPermRX mpl s`. -/
theorem fineHookBudgetPool_of_fineBudgetPool (γ : GhostName)
    (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (st : FineBudget) (s : State)
    (hrx : lim.enforced = true → CodeBlocksPermRX mpl s) :
    VerifiedLibraries.mallocngLib.codeRO mpl ∗
        (fineRustCliAllocBudget γ mpl tp brkStart).pool lim st s ⊢
      (fineHookRustCliAllocBudget γ mpl tp brkStart).pool lim st s := by
  change VerifiedLibraries.mallocngLib.codeRO mpl ∗
      (fineRustCliAllocBudget γ mpl tp brkStart).pool lim st s ⊢
    VerifiedLibraries.mallocngLib.codeRO mpl ∗
      (fineRustCliAllocBudget γ mpl tp brkStart).pool lim st s ∗
      ⌜lim.enforced = true → CodeBlocksPermRX mpl s⌝
  exact Entails.trans (Entails.pure_right hrx (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

/-- Startup pool initialization paired with compiled `__rustc::__rust_{alloc,dealloc,realloc}` and
    `__rustc::__rust_alloc_zeroed` entry contracts over `fineHookRustCliAllocBudget`. -/
theorem fineHookRustCliAllocZeroedBudget_thunk_of_placed_init
    {P : Program} {mpl : Obj.MultiPlacement}
    {thunkAddrs rdlAddrs : RustAllocAddrs}
    {allocZeroedThunkAddr allocZeroedRdlAddr memcpyAddr memsetAddr : BitVec 64}
    (tp brkStart auxvPtr : BitVec 64) (lim : BudgetLimits)
    (staticIvs : List (BitVec 64 × Nat)) (R : SepProp) (s0 : State)
    (hP : ProgContainsMallocng P mpl)
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem)
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hZeroThunk : hasInstrs P allocZeroedThunkAddr [ .b (allocZeroedRdlAddr - allocZeroedThunkAddr) ])
    (hZeroCode : hasInstrs P allocZeroedRdlAddr
      (rdlAllocZeroedInstrs allocZeroedRdlAddr (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc")
        (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec)
    (htpLo : 0xa4 ≤ tp.toNat) (htpHi : tp.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf brkStart)
    (htp : s0.tpidrEl0 = tp) (hbrkStart : s0.brkStart = brkStart) (hbrk : s0.brk = brkStart)
    (hInv : mallocngBudgetPoolInv lim staticIvs [] s0)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) tp ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineHookRustCliAllocBudget γ mpl tp brkStart
      (s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R) ∧
      RustCliAllocBudgetEntriesBase fineCostModel A P thunkAddrs ∧
      subroutine_ok P allocZeroedThunkAddr (rustAllocZeroedBudgetSpecBase fineCostModel A lim) := by
  obtain ⟨γ, hPool, _⟩ :=
    fineRustCliAllocBudgetEntries_thunks_of_placed_init tp brkStart auxvPtr lim staticIvs R s0
      hP hThunks hShims hMemcpy htpLo htpHi hbrkWf htp hbrkStart hbrk hInv hmem
  exact ⟨γ, fineHookBudgetPool_of_codeLoaded hCL hPool,
    fineHookRustCliAllocBudgetEntries_thunks hP γ tp brkStart hThunks hShims hMemcpy,
    fineHookRustCliAllocZeroedBudget_thunk_ok hP γ tp brkStart
      allocZeroedThunkAddr allocZeroedRdlAddr memsetAddr lim hZeroThunk hZeroCode hMemset⟩

/-! ## `AllocHooksBudget` and `TripleRatchetHooksBudget` -/

/-- Assemble `AllocHooksBudget fineCostModel A lim abs` from the three `HookSat` components for any
    `A : RustCliAllocBudget fineCostModel`. -/
theorem fineAllocHooksBudget_mk {A : RustCliAllocBudget fineCostModel}
    {lim : BudgetLimits} {abs : String → Option (State → State)}
    (hAlloc : HookSat abs "__rustc::__rust_alloc" (rustCliAllocBudgetSpecBase fineCostModel A lim false))
    (hDealloc : HookSat abs "__rustc::__rust_dealloc" (rustCliDeallocBudgetSpecBase fineCostModel A lim))
    (hRealloc : HookSat abs "__rustc::__rust_realloc" (rustCliReallocBudgetSpecBase fineCostModel A lim)) :
    AllocHooksBudgetBase fineCostModel A lim abs :=
  ⟨hAlloc, hDealloc, hRealloc⟩

/-- Instantiate `AllocHooksBudget` over `fineHookRustCliAllocBudget` from a limit-polymorphic
    `RustCliAllocBudgetHooks` witness. -/
theorem fineAllocHooksBudget_of_b2 (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {abs : String → Option (State → State)}
    (hHooks : RustCliAllocBudgetHooksBase fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) abs) :
    AllocHooksBudgetBase fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim abs :=
  ⟨hHooks.alloc lim, hHooks.dealloc lim, hHooks.realloc lim⟩

/-- Instantiate `AllocHooksBudget` over the raw `fineRustCliAllocBudget` from a limit-polymorphic
    `RustCliAllocBudgetHooks` witness. -/
theorem fineAllocHooksBudget_raw_of_b2 (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {abs : String → Option (State → State)}
    (hHooks : RustCliAllocBudgetHooksBase fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) abs) :
    AllocHooksBudgetBase fineCostModel (fineRustCliAllocBudget γ mpl tp brkStart) lim abs :=
  ⟨hHooks.alloc lim, hHooks.dealloc lim, hHooks.realloc lim⟩

/-- Instantiate `TripleRatchetHooksBudget` over `fineHookRustCliAllocBudget`, discharging `aesEnc`,
    `aesDec`, `formatInner`, and `fmtWrite` from `Placeable mpl` and the hook lookup equations. -/
theorem fineTripleRatchetHooksBudget_of_b2 [LibsignalPlacement]
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (S : SpqrModel) {abs : String → Option (State → State)}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hAlloc : AllocHooksBudget fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim abs)
    (hAllocZeroed : HookSat abs allocZeroedName
      (rustAllocZeroedBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim))
    (hAesEnc : abs aesEncName = some (aesEncHookMallocng mpl C.E))
    (hAesDec : abs aesDecName = some (aesDecHookMallocng mpl C.D))
    (hFormatInner : abs formatInnerName = some CryptoVerification.E2E.formatInnerHook0)
    (hFmtWrite : abs fmtWriteName = some CryptoVerification.E2E.fmtWriteHook0) :
    TripleRatchetHooksBudget C fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim S abs where
  alloc := hAlloc
  allocZeroed := hAllocZeroed
  aesEnc := fineAesEnc_budget_hookSat γ tp brkStart lim hPl C.E hAesEnc
  aesDec := fineAesDec_budget_hookSat γ tp brkStart lim hPl C.D hAesDec
  formatInner := hookSat_of_hookOk hFormatInner
    (formatInnerHook0_budget_ok fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)
  fmtWrite := hookSat_of_hookOk hFmtWrite
    (fmtWriteHook0_budget_ok fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)

/-- Raw `(fineCostModel, fineRustCliAllocBudget γ mpl tp brkStart)` counterpart of
    `fineTripleRatchetHooksBudget_of_b2`, discharging `formatInner` and `fmtWrite` concretely and
    accepting `HookSat` witnesses for `alloc`, `allocZeroed`, `aesEnc`, and `aesDec`. -/
theorem fineTripleRatchetHooksBudget_raw [LibsignalPlacement]
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (S : SpqrModel) {abs : String → Option (State → State)}
    (hAlloc : AllocHooksBudget fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim abs)
    (hAllocZeroed : HookSat abs allocZeroedName
      (rustAllocZeroedBudgetSpec fineCostModel
        (fineRustCliAllocBudget γ mpl tp brkStart) lim))
    (hAesEnc : HookSat abs aesEncName
      (aesEncBudgetSpec C.E fineCostModel
        (fineRustCliAllocBudget γ mpl tp brkStart) lim))
    (hAesDec : HookSat abs aesDecName
      (aesDecBudgetSpec C.D fineCostModel
        (fineRustCliAllocBudget γ mpl tp brkStart) lim))
    (hFormatInner : abs formatInnerName = some CryptoVerification.E2E.formatInnerHook0)
    (hFmtWrite : abs fmtWriteName = some CryptoVerification.E2E.fmtWriteHook0) :
    TripleRatchetHooksBudget C fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim S abs where
  alloc := hAlloc
  allocZeroed := hAllocZeroed
  aesEnc := hAesEnc
  aesDec := hAesDec
  formatInner := hookSat_of_hookOk hFormatInner
    (formatInnerHook0_budget_ok fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim)
  fmtWrite := hookSat_of_hookOk hFmtWrite
    (fmtWriteHook0_budget_ok fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim)

/-! ## `PublicApiHooksNoSessionStoreBudget` and `PublicApiHooksBudget` -/

/-- Instantiate `PublicApiHooksNoSessionStoreBudget` over `fineHookRustCliAllocBudget`, discharging
    `TripleRatchetHooksBudget`, `timeAdd`, and `stringClone`. -/
theorem finePublicApiHooksNoSessionStoreBudget_of_b2 [LibsignalPlacement]
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (S : SpqrModel) {abs : String → Option (State → State)}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hAlloc : AllocHooksBudget fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim abs)
    (hAllocZeroed : HookSat abs allocZeroedName
      (rustAllocZeroedBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim))
    (hAesEnc : abs aesEncName = some (aesEncHookMallocng mpl C.E))
    (hAesDec : abs aesDecName = some (aesDecHookMallocng mpl C.D))
    (hFormatInner : abs formatInnerName = some CryptoVerification.E2E.formatInnerHook0)
    (hFmtWrite : abs fmtWriteName = some CryptoVerification.E2E.fmtWriteHook0)
    (hTimeAdd : abs timeAddHookName = some CryptoVerification.E2E.timeAddHook)
    (hDurationSince : HookSat abs durationSinceHookName durationSinceBudgetSpec)
    (hStringClone : abs stringCloneHookName = some (stringCloneHookMallocng mpl)) :
    PublicApiHooksNoSessionStoreBudget C fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim S abs where
  toTripleRatchetHooksBudget :=
    fineTripleRatchetHooksBudget_of_b2 C γ tp brkStart lim S hPl hAlloc hAllocZeroed
      hAesEnc hAesDec hFormatInner hFmtWrite
  timeAdd := hookSat_of_hookOk hTimeAdd timeAddHook_budget_ok
  durationSince := hDurationSince
  stringClone := fineStringClone_budget_hookSat γ tp brkStart lim hPl hStringClone

/-- Specialization of `finePublicApiHooksNoSessionStoreBudget_of_b2` when `durationSinceHookName`
    maps to `hookNoop` (the E2E public-API stub). -/
theorem finePublicApiHooksNoSessionStoreBudget_noopDuration_of_b2 [LibsignalPlacement]
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (S : SpqrModel) {abs : String → Option (State → State)}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hAlloc : AllocHooksBudget fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim abs)
    (hAllocZeroed : HookSat abs allocZeroedName
      (rustAllocZeroedBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim))
    (hAesEnc : abs aesEncName = some (aesEncHookMallocng mpl C.E))
    (hAesDec : abs aesDecName = some (aesDecHookMallocng mpl C.D))
    (hFormatInner : abs formatInnerName = some CryptoVerification.E2E.formatInnerHook0)
    (hFmtWrite : abs fmtWriteName = some CryptoVerification.E2E.fmtWriteHook0)
    (hTimeAdd : abs timeAddHookName = some CryptoVerification.E2E.timeAddHook)
    (hDurationSince : abs durationSinceHookName = some hookNoop)
    (hStringClone : abs stringCloneHookName = some (stringCloneHookMallocng mpl)) :
    PublicApiHooksNoSessionStoreBudget C fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim S abs :=
  finePublicApiHooksNoSessionStoreBudget_of_b2 C γ tp brkStart lim S hPl hAlloc hAllocZeroed
    hAesEnc hAesDec hFormatInner hFmtWrite hTimeAdd
    (hookSat_of_hookOk hDurationSince hookNoop_durationSinceBudget_ok) hStringClone

/-- Instantiate full `PublicApiHooksBudget` over `(fineCostModel,
    fineHookRustCliAllocBudget γ mpl tp brkStart)` from `PublicApiHooksNoSessionStoreBudget` plus
    the four store-callback `HookSat` witnesses. -/
theorem finePublicApiHooksBudget_of_b2 [LibsignalPlacement]
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    {abs : String → Option (State → State)}
    (storeEnv : PublicApiStoreEnv := defaultPublicApiStoreEnv)
    (hBase : PublicApiHooksNoSessionStoreBudget C fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim S abs)
    (hLoad : HookSat abs loadSessionHookName
      (loadSessionBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim encRecord storeEnv.loadEnv))
    (hStore : HookSat abs storeSessionHookName
      (storeSessionBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim encRecord storeEnv.storeEnv))
    (hTrust : HookSat abs isTrustedHookName
      (isTrustedBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim storeEnv.trustEnv))
    (hSave : HookSat abs saveIdentityHookName
      (saveIdentityBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim storeEnv.saveEnv)) :
    PublicApiHooksBudget C fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim S encRecord abs storeEnv where
  toPublicApiHooksNoSessionStoreBudget := hBase
  loadSession := hLoad
  storeSession := hStore
  isTrusted := hTrust
  saveIdentity := hSave

/-- Raw `(fineCostModel, fineRustCliAllocBudget γ mpl tp brkStart)` counterpart of
    `finePublicApiHooksNoSessionStoreBudget_of_b2`. -/
theorem finePublicApiHooksNoSessionStoreBudget_raw [LibsignalPlacement]
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (S : SpqrModel) {abs : String → Option (State → State)}
    (hTr : TripleRatchetHooksBudget C fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim S abs)
    (hTimeAdd : abs timeAddHookName = some CryptoVerification.E2E.timeAddHook)
    (hDurationSince : HookSat abs durationSinceHookName durationSinceBudgetSpec)
    (hStringClone : HookSat abs stringCloneHookName
      (stringCloneBudgetSpec fineCostModel
        (fineRustCliAllocBudget γ mpl tp brkStart) lim)) :
    PublicApiHooksNoSessionStoreBudget C fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim S abs where
  toTripleRatchetHooksBudget := hTr
  timeAdd := hookSat_of_hookOk hTimeAdd timeAddHook_budget_ok
  durationSince := hDurationSince
  stringClone := hStringClone

/-- Raw `(fineCostModel, fineRustCliAllocBudget γ mpl tp brkStart)` counterpart of
    `finePublicApiHooksBudget_of_b2`. -/
theorem finePublicApiHooksBudget_raw [LibsignalPlacement]
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    {abs : String → Option (State → State)}
    (storeEnv : PublicApiStoreEnv := defaultPublicApiStoreEnv)
    (hBase : PublicApiHooksNoSessionStoreBudget C fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim S abs)
    (hLoad : HookSat abs loadSessionHookName
      (loadSessionBudgetSpec fineCostModel
        (fineRustCliAllocBudget γ mpl tp brkStart) lim encRecord storeEnv.loadEnv))
    (hStore : HookSat abs storeSessionHookName
      (storeSessionBudgetSpec fineCostModel
        (fineRustCliAllocBudget γ mpl tp brkStart) lim encRecord storeEnv.storeEnv))
    (hTrust : HookSat abs isTrustedHookName
      (isTrustedBudgetSpec fineCostModel
        (fineRustCliAllocBudget γ mpl tp brkStart) lim storeEnv.trustEnv))
    (hSave : HookSat abs saveIdentityHookName
      (saveIdentityBudgetSpec fineCostModel
        (fineRustCliAllocBudget γ mpl tp brkStart) lim storeEnv.saveEnv)) :
    PublicApiHooksBudget C fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim S encRecord abs storeEnv where
  toPublicApiHooksNoSessionStoreBudget := hBase
  loadSession := hLoad
  storeSession := hStore
  isTrusted := hTrust
  saveIdentity := hSave

/-! ## SPQR V1 Hook Bundles -/

/-- The 8 SPQR V1 hook contracts (`7` incremental ML-KEM-768 hooks with `withVmPreserved` plus
    `libcrux_hmac::hmac`). -/
structure FineSpqrB2Hooks (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (K : MlKem) (abs : String → Option (State → State)) : Prop where
  fromSeed : HookSat abs mlkemFromSeedName (withVmPreserved (mlkemFromSeedSpec K))
  pk1 : HookSat abs mlkemPk1Name (withVmPreserved mlkemPk1Spec)
  pk2 : HookSat abs mlkemPk2Name (withVmPreserved mlkemPk2Spec)
  encaps1 : HookSat abs mlkemEncaps1Name (withVmPreserved (mlkemEncaps1Spec K))
  encaps2 : HookSat abs mlkemEncaps2Name (withVmPreserved (mlkemEncaps2Spec K))
  decaps : HookSat abs mlkemDecapsName (withVmPreserved (mlkemDecapsSpec K))
  validatePk : HookSat abs mlkemValidatePkName (withVmPreserved (mlkemValidatePkSpec K))
  hmac : HookSat abs libcruxHmacName (libcruxHmacBudgetSpec C.F M A lim)

/-- Project `SpqrHooksBudget` to `FineSpqrB2Hooks`. -/
theorem SpqrHooksBudget.toFineSpqrB2Hooks {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)}
    (h : SpqrHooksBudget C M A lim K abs) :
    FineSpqrB2Hooks C M A lim K abs where
  fromSeed := h.fromSeed
  pk1 := h.pk1
  pk2 := h.pk2
  encaps1 := h.encaps1
  encaps2 := h.encaps2
  decaps := h.decaps
  validatePk := h.validatePk
  hmac := h.hmac

/-- Instantiate `FineSpqrB2Hooks` over `fineHookRustCliAllocBudget` from `Placeable mpl` and the 8
    SPQR hook lookup equations. -/
theorem fineSpqrB2Hooks_of_b2
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (K : MlKem) {abs : String → Option (State → State)}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hFromSeed : abs mlkemFromSeedName = some (CryptoVerification.E2E.mlkemFromSeedHook K))
    (hPk1 : abs mlkemPk1Name = some CryptoVerification.E2E.mlkemPk1Hook)
    (hPk2 : abs mlkemPk2Name = some CryptoVerification.E2E.mlkemPk2Hook)
    (hEncaps1 : abs mlkemEncaps1Name = some (CryptoVerification.E2E.mlkemEncaps1Hook K))
    (hEncaps2 : abs mlkemEncaps2Name = some (CryptoVerification.E2E.mlkemEncaps2Hook K))
    (hDecaps : abs mlkemDecapsName = some (CryptoVerification.E2E.mlkemDecapsHook K))
    (hValidatePk : abs mlkemValidatePkName = some (CryptoVerification.E2E.mlkemValidatePkHook K))
    (hHmac : abs libcruxHmacName = some (libcruxHmacHookMallocng mpl C.F)) :
    FineSpqrB2Hooks C fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim K abs where
  fromSeed := hookSat_of_hookOk hFromSeed (mlkemFromSeedHook_budget_ok K)
  pk1 := hookSat_of_hookOk hPk1 mlkemPk1Hook_budget_ok
  pk2 := hookSat_of_hookOk hPk2 mlkemPk2Hook_budget_ok
  encaps1 := hookSat_of_hookOk hEncaps1 (mlkemEncaps1Hook_budget_ok K)
  encaps2 := hookSat_of_hookOk hEncaps2 (mlkemEncaps2Hook_budget_ok K)
  decaps := hookSat_of_hookOk hDecaps (mlkemDecapsHook_budget_ok K)
  validatePk := hookSat_of_hookOk hValidatePk (mlkemValidatePkHook_budget_ok K)
  hmac := fineLibcruxHmac_budget_hookSat γ tp brkStart lim hPl C.F hHmac

/-- Raw `(fineCostModel, fineRustCliAllocBudget γ mpl tp brkStart)` counterpart of
    `fineSpqrB2Hooks_of_b2`, discharging all 7 ML-KEM-768 hooks concretely and taking `hHmac` as a
    `HookSat` witness. -/
theorem fineSpqrB2Hooks_raw
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (K : MlKem) {abs : String → Option (State → State)}
    (hFromSeed : abs mlkemFromSeedName = some (CryptoVerification.E2E.mlkemFromSeedHook K))
    (hPk1 : abs mlkemPk1Name = some CryptoVerification.E2E.mlkemPk1Hook)
    (hPk2 : abs mlkemPk2Name = some CryptoVerification.E2E.mlkemPk2Hook)
    (hEncaps1 : abs mlkemEncaps1Name = some (CryptoVerification.E2E.mlkemEncaps1Hook K))
    (hEncaps2 : abs mlkemEncaps2Name = some (CryptoVerification.E2E.mlkemEncaps2Hook K))
    (hDecaps : abs mlkemDecapsName = some (CryptoVerification.E2E.mlkemDecapsHook K))
    (hValidatePk : abs mlkemValidatePkName = some (CryptoVerification.E2E.mlkemValidatePkHook K))
    (hHmac : HookSat abs libcruxHmacName
      (libcruxHmacBudgetSpec C.F fineCostModel
        (fineRustCliAllocBudget γ mpl tp brkStart) lim)) :
    FineSpqrB2Hooks C fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim K abs where
  fromSeed := hookSat_of_hookOk hFromSeed (mlkemFromSeedHook_budget_ok K)
  pk1 := hookSat_of_hookOk hPk1 mlkemPk1Hook_budget_ok
  pk2 := hookSat_of_hookOk hPk2 mlkemPk2Hook_budget_ok
  encaps1 := hookSat_of_hookOk hEncaps1 (mlkemEncaps1Hook_budget_ok K)
  encaps2 := hookSat_of_hookOk hEncaps2 (mlkemEncaps2Hook_budget_ok K)
  decaps := hookSat_of_hookOk hDecaps (mlkemDecapsHook_budget_ok K)
  validatePk := hookSat_of_hookOk hValidatePk (mlkemValidatePkHook_budget_ok K)
  hmac := hHmac

/-- Implication from `FineSpqrB2Hooks` to `SpqrHooksBudget`. -/
def SpqrHooksB2Residual (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (K : MlKem) (abs : String → Option (State → State)) : Prop :=
  FineSpqrB2Hooks C M A lim K abs → SpqrHooksBudget C M A lim K abs

/-- Instantiate `SpqrHooksBudget` over `fineHookRustCliAllocBudget` via `FineSpqrB2Hooks`. -/
theorem fineSpqrHooksBudget_of_b2
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (K : MlKem) {abs : String → Option (State → State)}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hFromSeed : abs mlkemFromSeedName = some (CryptoVerification.E2E.mlkemFromSeedHook K))
    (hPk1 : abs mlkemPk1Name = some CryptoVerification.E2E.mlkemPk1Hook)
    (hPk2 : abs mlkemPk2Name = some CryptoVerification.E2E.mlkemPk2Hook)
    (hEncaps1 : abs mlkemEncaps1Name = some (CryptoVerification.E2E.mlkemEncaps1Hook K))
    (hEncaps2 : abs mlkemEncaps2Name = some (CryptoVerification.E2E.mlkemEncaps2Hook K))
    (hDecaps : abs mlkemDecapsName = some (CryptoVerification.E2E.mlkemDecapsHook K))
    (hValidatePk : abs mlkemValidatePkName = some (CryptoVerification.E2E.mlkemValidatePkHook K))
    (hHmac : abs libcruxHmacName = some (libcruxHmacHookMallocng mpl C.F))
    (hRes : SpqrHooksB2Residual C fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim K abs) :
    SpqrHooksBudget C fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim K abs :=
  hRes (fineSpqrB2Hooks_of_b2 C γ tp brkStart lim K hPl
    hFromSeed hPk1 hPk2 hEncaps1 hEncaps2 hDecaps hValidatePk hHmac)

/-- Raw `(fineCostModel, fineRustCliAllocBudget γ mpl tp brkStart)` counterpart of
    `fineSpqrHooksBudget_of_b2`. -/
theorem fineSpqrHooksBudget_raw
    (C : Crypto) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (K : MlKem) {abs : String → Option (State → State)}
    (hFromSeed : abs mlkemFromSeedName = some (CryptoVerification.E2E.mlkemFromSeedHook K))
    (hPk1 : abs mlkemPk1Name = some CryptoVerification.E2E.mlkemPk1Hook)
    (hPk2 : abs mlkemPk2Name = some CryptoVerification.E2E.mlkemPk2Hook)
    (hEncaps1 : abs mlkemEncaps1Name = some (CryptoVerification.E2E.mlkemEncaps1Hook K))
    (hEncaps2 : abs mlkemEncaps2Name = some (CryptoVerification.E2E.mlkemEncaps2Hook K))
    (hDecaps : abs mlkemDecapsName = some (CryptoVerification.E2E.mlkemDecapsHook K))
    (hValidatePk : abs mlkemValidatePkName = some (CryptoVerification.E2E.mlkemValidatePkHook K))
    (hHmac : HookSat abs libcruxHmacName
      (libcruxHmacBudgetSpec C.F fineCostModel
        (fineRustCliAllocBudget γ mpl tp brkStart) lim))
    (hRes : SpqrHooksB2Residual C fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim K abs) :
    SpqrHooksBudget C fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) lim K abs :=
  hRes (fineSpqrB2Hooks_raw C γ tp brkStart lim K
    hFromSeed hPk1 hPk2 hEncaps1 hEncaps2 hDecaps hValidatePk hHmac)

/-! ## Allocator/Crypto Slice and Full `CliExternsBudgetOk` -/

/-- Lookup equations and `memset`/`memcpy` `HookSat` contracts for the non-I/O-allocating rows of
    an extern table `ext` using shared-pool crypto and `String::clone` hooks. -/
structure FineCliB2ExternRows [LibsignalPlacement] (mpl : Obj.MultiPlacement) (W : CliHooks)
    (ext : String → Option (State → State)) : Prop where
  shim : ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" = some hookNoop
  memset : HookSat ext "memset" memsetSpec
  memmove : ext "memmove" = some hookMemmove
  memcpy : HookSat ext "memcpy" memcpySpec
  memcpyRO : HookSat ext "memcpy" memcpyROSpec
  bcmp : ext "bcmp" = some (cliBcmpHook W.bcmp)
  strlen : ext "strlen" = some strlenHook
  writeFile : ext writeFileName = some writeFileHook
  writeStdout : ext writeStdoutName = some writeStdoutHook
  memrchr : ext "core::slice::memchr::memrchr" = some memrchrHook
  fromUtf8 : ext "core::str::converts::from_utf8" = some (fromUtf8Hook W.utf8Err)
  stringClone : ext stringCloneHookName = some (stringCloneHookMallocng mpl)
  fmtWrite : ext fmtWriteName = some CryptoVerification.E2E.fmtWriteHook0
  formatInner : ext formatInnerName = some CryptoVerification.E2E.formatInnerHook0
  durationSince : ext durationSinceHookName = some durationSinceExactHook
  timeAdd : ext timeAddHookName = some CryptoVerification.E2E.timeAddHook
  blackBox : ext "subtle::black_box::<u8>" = some CryptoVerification.LibsignalSession.blackBoxHook
  compress256 : ext "sha2::sha256::compress256" =
    some (CryptoVerification.LibsignalHmac.compress256Hook W.C.F)
  aesEnc : ext aesEncName = some (aesEncHookMallocng mpl W.C.E)
  aesDec : ext aesDecName = some (aesDecHookMallocng mpl W.C.D)
  pubFromSecret : ext pubFromSecretName =
    some (CryptoVerification.LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey)
  dh : ext dhName = some (CryptoVerification.LibsignalTripleRatchet.diffieHellmanHook W.C.X)
  staticDrop : ext staticDropName = some CryptoVerification.LibsignalTripleRatchet.zeroizeSecretHook
  sharedDrop : ext sharedDropName = some CryptoVerification.LibsignalTripleRatchet.zeroizeSecretHook
  compress512 : ext compress512Name = some (CryptoVerification.E2E.compress512Hook W.Q.F512)
  toEdwards : ext toEdwardsName = some (CryptoVerification.E2E.toEdwardsHook W.Q.montToEd)
  compress : ext compressName = some (CryptoVerification.E2E.compressHook W.Q.compress)
  edNeg : ext edNegName = some (CryptoVerification.E2E.edNegHook W.Q.edNeg)
  torsionFree : ext torsionFreeName =
    some (CryptoVerification.E2E.torsionFreeHook W.Q.isTorsionFree)
  dsmb : ext dsmbName = some (CryptoVerification.E2E.dsmbHook W.Q.dsmb)
  scalarMod : ext scalarModName = some (CryptoVerification.E2E.scalarModHook W.Q.scalarMod)
  scalarWide : ext scalarWideName = some (CryptoVerification.E2E.scalarWideHook W.Q.scalarWide)
  kemEncaps : ext kemEncapsName = some (CryptoVerification.E2E.kemEncapsHook W.Q.encaps)
  kemDecaps : ext kemDecapsName = some (CryptoVerification.E2E.kemDecapsHook W.Q.decaps)
  mlkemFromSeed : ext mlkemFromSeedName = some (CryptoVerification.E2E.mlkemFromSeedHook W.Q.K)
  mlkemPk1 : ext mlkemPk1Name = some CryptoVerification.E2E.mlkemPk1Hook
  mlkemPk2 : ext mlkemPk2Name = some CryptoVerification.E2E.mlkemPk2Hook
  mlkemEncaps1 : ext mlkemEncaps1Name = some (CryptoVerification.E2E.mlkemEncaps1Hook W.Q.K)
  mlkemEncaps2 : ext mlkemEncaps2Name = some (CryptoVerification.E2E.mlkemEncaps2Hook W.Q.K)
  mlkemDecaps : ext mlkemDecapsName = some (CryptoVerification.E2E.mlkemDecapsHook W.Q.K)
  mlkemValidatePk : ext mlkemValidatePkName =
    some (CryptoVerification.E2E.mlkemValidatePkHook W.Q.K)
  libcruxHmac : ext libcruxHmacName = some (libcruxHmacHookMallocng mpl W.C.F)

/-- Allocator, libc, `core`/`std`, write-I/O, session-crypto, PQXDH, and SPQR slice of
    `CliExternsBudgetOk`. -/
structure FineCliExternsAllocSlice [LibsignalPlacement] (P : PEParams) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  shim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" shimSpec
  alloc : AllocHooksBudget M A lim ext
  allocZeroed : HookSat ext allocZeroedName (rustAllocZeroedBudgetSpec M A lim)
  memset : HookSat ext "memset" memsetSpec
  memmove : HookSat ext "memmove" memmoveSpec
  memcpy : HookSat ext "memcpy" memcpySpec
  memcpyRO : HookSat ext "memcpy" memcpyROSpec
  bcmp : HookSat ext "bcmp" bcmpSpec
  strlen : HookSat ext "strlen" strlenSpec
  writeFile : ∀ img, HookSat ext writeFileName (writeFileBudgetSpec M A lim img)
  writeStdout : ∀ img, HookSat ext writeStdoutName (writeStdoutBudgetSpec M A lim img)
  memrchr : HookSat ext "core::slice::memchr::memrchr" memrchrSpec
  fromUtf8 : HookSat ext "core::str::converts::from_utf8" fromUtf8Spec
  stringClone : HookSat ext stringCloneHookName (stringCloneBudgetSpec M A lim)
  fmtWrite : HookSat ext fmtWriteName (fmtWriteBudgetSpec M A lim)
  formatInner : HookSat ext formatInnerName (formatInnerBudgetSpec M A lim)
  durationSince : HookSat ext durationSinceHookName durationSinceEpochBudgetSpec
  timeAdd : HookSat ext timeAddHookName timeAddBudgetSpec
  blackBox : HookSat ext "subtle::black_box::<u8>" blackBoxSpec
  compress256 : HookSat ext "sha2::sha256::compress256" (compress256Spec P.C)
  aesEnc : HookSat ext aesEncName (aesEncBudgetSpec P.C.E M A lim)
  aesDec : HookSat ext aesDecName (aesDecBudgetSpec P.C.D M A lim)
  pubFromSecret : HookSat ext pubFromSecretName (pubFromSecretSpec P.C)
  dh : HookSat ext dhName (dhSpec P.C)
  staticDrop : HookSat ext staticDropName zeroizeSpec
  sharedDrop : HookSat ext sharedDropName zeroizeSpec
  compress512 : HookSat ext compress512Name (compress512Spec P.Q)
  toEdwards : HookSat ext toEdwardsName (toEdwardsSpec P.Q)
  compress : HookSat ext compressName (pureByteFunctionSpec P.Q.compress false)
  edNeg : HookSat ext edNegName (pureByteFunctionSpec P.Q.edNeg true)
  torsionFree : HookSat ext torsionFreeName (torsionFreeSpec P.Q)
  dsmb : HookSat ext dsmbName (dsmbSpec P.Q)
  scalarMod : HookSat ext scalarModName (pureByteFunctionSpec P.Q.scalarMod true)
  scalarWide : HookSat ext scalarWideName (pureByteFunctionSpec P.Q.scalarWide false)
  kemEncaps : HookSat ext kemEncapsName (kemEncapsSpec P.Q)
  kemDecaps : HookSat ext kemDecapsName (kemDecapsSpec P.Q)
  spqrB2 : FineSpqrB2Hooks P.C M A lim P.Q.K ext

/-- Instantiate `FineCliExternsAllocSlice` over `fineHookRustCliAllocBudget` from `Placeable mpl`,
    `alloc`, `allocZeroed`, and `FineCliB2ExternRows mpl W ext`. -/
theorem fineCliExternsBudgetAllocSlice [LibsignalPlacement]
    (W : CliHooks) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {ext : String → Option (State → State)}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hAlloc : AllocHooksBudget fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim ext)
    (hAllocZeroed : HookSat ext allocZeroedName
      (rustAllocZeroedBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim))
    (hRows : FineCliB2ExternRows mpl W ext) :
    FineCliExternsAllocSlice ⟨W.C, W.Q⟩ fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim ext where
  shim := hookSat_of_hookOk hRows.shim cliShim_hookOk
  alloc := hAlloc
  allocZeroed := hAllocZeroed
  memset := hRows.memset
  memmove := hookSat_of_hookOk hRows.memmove cliMemmove_hookOk
  memcpy := hRows.memcpy
  memcpyRO := hRows.memcpyRO
  bcmp := hookSat_of_hookOk hRows.bcmp (cliBcmp_hookOk W)
  strlen := hookSat_of_hookOk hRows.strlen cliStrlen_hookOk
  writeFile img := hookSat_writeFileBudget_of_hookSat
    (fineHookRustCliAllocBudget γ mpl tp brkStart) lim
    (hookSat_of_hookOk hRows.writeFile (cliWriteFile_hookOk img))
    (fun _ hf s => (Option.some.inj (hRows.writeFile.symm.trans hf)) ▸ vmPreserved_writeFileHook s)
  writeStdout img := hookSat_writeStdoutBudget_of_hookSat
    (fineHookRustCliAllocBudget γ mpl tp brkStart) lim
    (hookSat_of_hookOk hRows.writeStdout (cliWriteStdout_hookOk img))
    (fun _ hf s => (Option.some.inj (hRows.writeStdout.symm.trans hf)) ▸ vmPreserved_writeStdoutHook s)
  memrchr := hookSat_of_hookOk hRows.memrchr cliMemrchr_hookOk
  fromUtf8 := hookSat_of_hookOk hRows.fromUtf8 (cliFromUtf8_hookOk W)
  stringClone := fineStringClone_budget_hookSat γ tp brkStart lim hPl hRows.stringClone
  fmtWrite := hookSat_of_hookOk hRows.fmtWrite
    (fmtWriteHook0_budget_ok fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)
  formatInner := hookSat_of_hookOk hRows.formatInner
    (formatInnerHook0_budget_ok fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)
  durationSince := hookSat_of_hookOk hRows.durationSince durationSinceExactHook_epoch_budget_ok
  timeAdd := hookSat_of_hookOk hRows.timeAdd timeAddHook_budget_ok
  blackBox := hookSat_of_hookOk hRows.blackBox cliBlackBox_hookOk
  compress256 := hookSat_of_hookOk hRows.compress256 (cliCompress256_hookOk W.C)
  aesEnc := fineAesEnc_budget_hookSat γ tp brkStart lim hPl W.C.E hRows.aesEnc
  aesDec := fineAesDec_budget_hookSat γ tp brkStart lim hPl W.C.D hRows.aesDec
  pubFromSecret := hookSat_of_hookOk hRows.pubFromSecret (cliPubFromSecret_hookOk W.C)
  dh := hookSat_of_hookOk hRows.dh (cliDh_hookOk W.C)
  staticDrop := hookSat_of_hookOk hRows.staticDrop cliZeroize_hookOk
  sharedDrop := hookSat_of_hookOk hRows.sharedDrop cliZeroize_hookOk
  compress512 := hookSat_of_hookOk hRows.compress512 (cliCompress512_hookOk W.Q)
  toEdwards := hookSat_of_hookOk hRows.toEdwards (cliToEdwards_hookOk W.Q)
  compress := hookSat_of_hookOk hRows.compress (cliCompress_hookOk W.Q)
  edNeg := hookSat_of_hookOk hRows.edNeg (cliEdNeg_hookOk W.Q)
  torsionFree := hookSat_of_hookOk hRows.torsionFree (cliTorsionFree_hookOk W.Q)
  dsmb := hookSat_of_hookOk hRows.dsmb (cliDsmb_hookOk W.Q)
  scalarMod := hookSat_of_hookOk hRows.scalarMod (cliScalarMod_hookOk W.Q)
  scalarWide := hookSat_of_hookOk hRows.scalarWide (cliScalarWide_hookOk W.Q)
  kemEncaps := hookSat_of_hookOk hRows.kemEncaps (cliKemEncaps_hookOk W.Q)
  kemDecaps := hookSat_of_hookOk hRows.kemDecaps (cliKemDecaps_hookOk W.Q)
  spqrB2 := fineSpqrB2Hooks_of_b2 W.C γ tp brkStart lim W.Q.K hPl
    hRows.mlkemFromSeed hRows.mlkemPk1 hRows.mlkemPk2 hRows.mlkemEncaps1
    hRows.mlkemEncaps2 hRows.mlkemDecaps hRows.mlkemValidatePk hRows.libcruxHmac

/-- Assemble `CliExternsBudgetOk` over `fineHookRustCliAllocBudget` from `FineCliB2ExternRows`,
    table-wide frame properties, `readFile` / `readStdin`, and `SpqrHooksB2Residual`. -/
theorem fineCliExternsBudgetOk_of_b2 [LibsignalPlacement]
    (W : CliHooks) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {ext : String → Option (State → State)}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hTpidr : ∀ n f, ext n = some f → ∀ s, (f s).tpidrEl0 = s.tpidrEl0)
    (hNoExec : ∀ n f, ext n = some f → ∀ s a, ((f s).mem.perm a).x → (s.mem.perm a).x)
    (hFsTraced : ∀ n f, ext n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    (hFsKept : ∀ n f, ext n = some f → n ∉ ioNames → ∀ s, (f s).fs = s.fs)
    (hVmKept : ∀ n f, ext n = some f → n ∉ cliAllocNames → ∀ s, VmPreserved s (f s))
    (hAlloc : AllocHooksBudget fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim ext)
    (hAllocZeroed : HookSat ext allocZeroedName
      (rustAllocZeroedBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim))
    (hReadFile : ∀ img, HookSat ext readFileName
      (readFileBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim img))
    (hReadStdin : ∀ img, HookSat ext readStdinName
      (readStdinBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim img))
    (hRows : FineCliB2ExternRows mpl W ext)
    (hSpqrRes : SpqrHooksB2Residual W.C fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim W.Q.K ext) :
    CliExternsBudgetOk ⟨W.C, W.Q⟩ fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim ext := by
  have hS := fineCliExternsBudgetAllocSlice W γ tp brkStart lim hPl hAlloc hAllocZeroed hRows
  exact
    { tpidr := hTpidr
      noExec := hNoExec
      fsTraced := hFsTraced
      fsKept := hFsKept
      vmKept := hVmKept
      shim := hS.shim
      alloc := hS.alloc
      allocZeroed := hS.allocZeroed
      memset := hS.memset
      memmove := hS.memmove
      memcpy := hS.memcpy
      memcpyRO := hS.memcpyRO
      bcmp := hS.bcmp
      strlen := hS.strlen
      readFile := hReadFile
      writeFile := hS.writeFile
      readStdin := hReadStdin
      writeStdout := hS.writeStdout
      memrchr := hS.memrchr
      fromUtf8 := hS.fromUtf8
      fmtWrite := hS.fmtWrite
      formatInner := hS.formatInner
      durationSince := hS.durationSince
      timeAdd := hS.timeAdd
      blackBox := hS.blackBox
      compress256 := hS.compress256
      aesEnc := hS.aesEnc
      aesDec := hS.aesDec
      pubFromSecret := hS.pubFromSecret
      dh := hS.dh
      staticDrop := hS.staticDrop
      sharedDrop := hS.sharedDrop
      compress512 := hS.compress512
      toEdwards := hS.toEdwards
      compress := hS.compress
      edNeg := hS.edNeg
      torsionFree := hS.torsionFree
      dsmb := hS.dsmb
      scalarMod := hS.scalarMod
      scalarWide := hS.scalarWide
      kemEncaps := hS.kemEncaps
      kemDecaps := hS.kemDecaps
      spqr := hSpqrRes hS.spqrB2 }

/-- Assemble full `CliExternsBudgetOk` over any `(fineCostModel, A)` (including raw
    `fineRustCliAllocBudget γ mpl tp brkStart`) from a `FineCliExternsAllocSlice` witness, the
    frame properties, `readFile` / `readStdin`, and `SpqrHooksB2Residual`. -/
theorem fineCliExternsBudgetOk_of_slice [LibsignalPlacement]
    {P : PEParams} {A : RustCliAllocBudget fineCostModel}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hTpidr : ∀ n f, ext n = some f → ∀ s, (f s).tpidrEl0 = s.tpidrEl0)
    (hNoExec : ∀ n f, ext n = some f → ∀ s a, ((f s).mem.perm a).x → (s.mem.perm a).x)
    (hFsTraced : ∀ n f, ext n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    (hFsKept : ∀ n f, ext n = some f → n ∉ ioNames → ∀ s, (f s).fs = s.fs)
    (hVmKept : ∀ n f, ext n = some f → n ∉ cliAllocNames → ∀ s, VmPreserved s (f s))
    (hReadFile : ∀ img, HookSat ext readFileName (readFileBudgetSpec fineCostModel A lim img))
    (hReadStdin : ∀ img, HookSat ext readStdinName (readStdinBudgetSpec fineCostModel A lim img))
    (hSlice : FineCliExternsAllocSlice P fineCostModel A lim ext)
    (hSpqrRes : SpqrHooksB2Residual P.C fineCostModel A lim P.Q.K ext) :
    CliExternsBudgetOk P fineCostModel A lim ext where
  tpidr := hTpidr
  noExec := hNoExec
  fsTraced := hFsTraced
  fsKept := hFsKept
  vmKept := hVmKept
  shim := hSlice.shim
  alloc := hSlice.alloc
  allocZeroed := hSlice.allocZeroed
  memset := hSlice.memset
  memmove := hSlice.memmove
  memcpy := hSlice.memcpy
  memcpyRO := hSlice.memcpyRO
  bcmp := hSlice.bcmp
  strlen := hSlice.strlen
  readFile := hReadFile
  writeFile := hSlice.writeFile
  readStdin := hReadStdin
  writeStdout := hSlice.writeStdout
  memrchr := hSlice.memrchr
  fromUtf8 := hSlice.fromUtf8
  fmtWrite := hSlice.fmtWrite
  formatInner := hSlice.formatInner
  durationSince := hSlice.durationSince
  timeAdd := hSlice.timeAdd
  blackBox := hSlice.blackBox
  compress256 := hSlice.compress256
  aesEnc := hSlice.aesEnc
  aesDec := hSlice.aesDec
  pubFromSecret := hSlice.pubFromSecret
  dh := hSlice.dh
  staticDrop := hSlice.staticDrop
  sharedDrop := hSlice.sharedDrop
  compress512 := hSlice.compress512
  toEdwards := hSlice.toEdwards
  compress := hSlice.compress
  edNeg := hSlice.edNeg
  torsionFree := hSlice.torsionFree
  dsmb := hSlice.dsmb
  scalarMod := hSlice.scalarMod
  scalarWide := hSlice.scalarWide
  kemEncaps := hSlice.kemEncaps
  kemDecaps := hSlice.kemDecaps
  spqr := hSpqrRes hSlice.spqrB2

end LibsignalBinary.Heap.Fine
