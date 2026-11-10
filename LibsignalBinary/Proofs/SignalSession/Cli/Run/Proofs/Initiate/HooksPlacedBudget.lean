/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Hook Bundle for `initiate`

Defines `RunHooksPlaced W A lim H` threading `RustCliAllocBudget M`, `BudgetLimits`, and
`VmPreserved` across all allocator, codec, serialization, memory, cryptographic, KEM, panic, and
`TraceFsSound` contracts, together with its constructor at `cliGhostExterns` and callee projections.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.E2E (bcmpName kemEncapsHook)
open CryptoVerification.E2E.HooksE (e2eBcmpSpec)
open CryptoVerification.E2E.Record.Placed (blkPl_52 lsProg_52)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalPublicApi.StoreKit (TraceFsSound)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet
  (HkdfPlacedHooks derivePublicKeyBytesSpec diffieHellmanSpec extHookStack framelessMemcpySpec
   hookMemcpy_eq_memcpyHook hookMemset_eq_memsetHook memcpyName memsetName noAllocShimSpec
   zeroizeSecretSpec)
open CryptoVerification.RecordCodecs.Placed (blkPl_18 blkPl_65 blkPl_84 lsProg_18 lsProg_65 lsProg_84)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced cliPanicSymbolsPlaced durationSinceExactHook lsBlackBoxSym
   lsCompress256Sym lsDiffieHellmanSym lsDurationSinceSym lsFormatInnerSym lsFromUtf8Sym
   lsMemcpySym lsMemrchrSym lsMemsetSym lsPubFromSecretSym lsRustAllocSymCli
   lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
   lsSharedSecretDropSym lsStaticSecretDropSym lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (cliBcmpName cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.MainHops (fromUtf8AsciiSpec memrchrSpec)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks IsFsC cliExternsPlaced_row cliGhostExterns cliGhostExterns_alloc
   cliGhostExterns_allocZeroed cliGhostExterns_dealloc cliGhostExterns_memcpy_some
   cliGhostExterns_memset_some cliGhostExterns_other
   cliGhostExterns_realloc cliGhostExterns_shim hookNoop_fsT hookSat_of_eq)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (lsKemEncapsSym traceFsSound_cliGhostPlaced)
open CryptoVerification.SignalSession.Cli.Slots
  (blackBox_row_placed cliGhostExterns_panic_all cliGhostExterns_panic_handle_alloc_error
   cliGhostExterns_panic_handle_error cliGhostExterns_sat_of_cliExternsPlaced
   compress256_row_placed durationSince_row_placed kemEncaps_row_placed)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.IfaceBudgetLemmas (perm_writeBytes_norm)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (allocMemcpyVmSpec rustAllocShimVmSpec stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (formatInnerBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
  (hookSat_sessionShimBudget_of_withVmPreserved identityKeyPair_tryFrom_placed_ok_of_hooks
   identityKey_decode_placed_ok_of_hooks portDepsPlaced_of_hooks
   preKeyRecord_deserialize_placed_ok_of_hooks)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (CodecHooksPlaced PortDepsPlaced identityKeyDecodePlacedSpec identityKeyPairTryFromPlacedSpec
   preKeyDeserializePlacedSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
  (EncodeRawPlacedOkX SerializePlacedOkX SessionClonePlacedOkX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget
  (encodeRaw_placed_cl_of_serContractsX encodeRaw_placed_ok_of_serContractsX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExtBudget
  (recordSerializeEnvSpecX recordSerializeSpecX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
  (SerContractsXPlaced SerializeEnvX encodeRawSpecX serializeSpecX)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (BaseHelperRows cliExternsPlaced_baseHelperRows
   cliGhostExterns_memmove_eq shim_budget_sat_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks allocContractsFsPlaced_of_hooks
   allocContractsXCliPlaced_of_hooks cliExternsPlaced_allocMemcpyVm_budget_sat
   cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_bcmp_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_derivePublicKeyBytes_budget_sat cliExternsPlaced_diffieHellman_budget_sat
   cliExternsPlaced_e2eBcmp_budget_sat cliExternsPlaced_framelessMemcpy_budget_sat
   cliExternsPlaced_memcpyRegionRO_budget_sat cliExternsPlaced_noAllocShim_budget_sat
   cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemcpy_budget_sat
   cliExternsPlaced_sessionMemmove_budget_sat cliExternsPlaced_sharedSecretDrop_budget_sat
   cliExternsPlaced_staticSecretDrop_budget_sat cliGhostExterns_sessionMemcpy_budget_sat
   codecHooksPlaced_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)

/-! ## Auxiliary `HkdfPlacedHooks` and memory-hook instances -/

/-- `HkdfPlacedHooks W.C.F H` constructor from explicit `memset`/`memcpy` hook equalities and
`compress256` matching the `37`-row `cliHookTablePlaced mmpl W`. -/
theorem instHkdfPlacedHooks_cli (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {H : LibsignalHooks}
    (hMs : H lsMemsetSym = some memsetHook)
    (hMc : H lsMemcpySym = some memcpyHook)
    (hComp : H lsCompress256Sym = cliExternsPlaced mmpl W lsCompress256Sym) :
    HkdfPlacedHooks W.C.F H where
  memset := hMs
  memcpy := hMc
  compress256 := hComp.trans (cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W))

/-- `HkdfPlacedHooks W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W))` when `g` carries
`some memsetHook` and `some memcpyHook` (stock-ghost only, e.g. `bumpGhost`/`a0Ghost`;
unsatisfiable at Narrow/K tuples, which use the planned WP6b `Sat` sibling). -/
theorem instHkdfPlacedHooks_cliGhost (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks)
    (hMs : g.memset = some memsetHook)
    (hMc : g.memcpy = some memcpyHook) :
    HkdfPlacedHooks W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  instHkdfPlacedHooks_cli mmpl W
    (cliGhostExterns_memset_some g _ hMs)
    (cliGhostExterns_memcpy_some g _ hMc)
    (cliGhostExterns_other g _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))

private theorem hookNoop_rustAllocShimVm_ok : HookOk hookNoop rustAllocShimVmSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  dsimp only [rustAllocShimVmSpec, hookNoop, retHook, id_eq] at hpre ⊢
  rw [emp_sepConj] at hpre
  rw [satisfies_pure_sepConj]
  exact ⟨⟨⟨by cases s0; rfl, by cases s0; rfl, by cases s0; rfl, by cases s0; rfl,
    by cases s0; rfl, by cases s0; rfl, by cases s0; rfl⟩,
    ⟨⟨by cases s0; rfl, by cases s0; rfl, by cases s0; rfl⟩,
     by cases s0; rfl, fun _ => by cases s0; rfl, fun _ _ _ => by cases s0; rfl⟩⟩, hpre⟩

private theorem hookMemcpy_allocCallPreserved (s : State) :
    AllocCallPreserved s (hookMemcpy s) := by
  unfold hookMemcpy retHook
  cases s
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem hookMemcpy_vmPreserved (s : State) :
    VmPreserved s (hookMemcpy s) := by
  unfold hookMemcpy retHook
  refine ⟨⟨by cases s; rfl, by cases s; rfl, by cases s; rfl⟩, by cases s; rfl, fun a => ?_,
    fun _ _ _ => by cases s; rfl⟩
  cases s
  exact congrFun (perm_writeBytes_norm _ _ _) a

private theorem hookMemcpy_allocMemcpyVm_ok : HookOk hookMemcpy allocMemcpyVmSpec := by
  intro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [allocMemcpyVmSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩
  have hx2' : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpre0 : s0.mem ⊨ memcpyRegionSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2'⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases hookMemcpy_region_ok (dst, src, bs) R s0 hrun hpre0 hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [memcpyRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    dsimp only [allocMemcpyVmSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.1, hookMemcpy_allocCallPreserved s0, hookMemcpy_vmPreserved s0⟩,
      by simpa only [sepConj_assoc] using hpost.2⟩
  · exact Or.inr hrest

theorem rustAllocShimVm_sat_of_eq (baseExt : LibsignalHooks) {g : CliGhostHooks}
    (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g baseExt) lsRustNoAllocShimSymCli rustAllocShimVmSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g baseExt).trans (congrArg some hShim),
    hookNoop_rustAllocShimVm_ok⟩

theorem cliExternsPlaced_rustAllocShimVm_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli
      rustAllocShimVmSpec :=
  rustAllocShimVm_sat_of_eq (cliExternsPlaced mmpl W) hShim

/-- Stock-ghost discharge helper for `hAllocMemcpyVm`: `HookSat H memcpyName allocMemcpyVmSpec`
when `H memcpyName = some hookMemcpy` (e.g. via `cliGhostExterns_memcpy_some`). -/
theorem cliExternsPlaced_allocMemcpyVm_sat {H : LibsignalHooks}
    (hmc : H memcpyName = some hookMemcpy) :
    HookSat H memcpyName allocMemcpyVmSpec :=
  ⟨hookMemcpy, hmc, hookMemcpy_allocMemcpyVm_ok⟩

theorem serContractsXPlaced_of_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (hBase : BaseHelperRows mmpl W baseExt)
    (hG : CliGhostAllocHooks M A lim g) :
    SerContractsXPlaced M A lim (cliGhostExterns g baseExt) :=
  SerContractsXPlaced.of_hooks
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    ⟨g.realloc, cliGhostExterns_realloc g baseExt, hG.realloc⟩
    (shim_budget_sat_of_eq baseExt hG.shim_eq)
    (hookSat_of_eq (cliGhostExterns_memmove_eq mmpl W g hBase)
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W extHookStack))
    (cliGhostExterns_sessionMemcpy_budget_sat baseExt hG extHookStack)

theorem serContractsXPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    SerContractsXPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  serContractsXPlaced_of_ghost mmpl W (cliExternsPlaced mmpl W) g
    (cliExternsPlaced_baseHelperRows mmpl W) hG

/-! ## Budget-threaded `RunHooksPlaced` bundle -/

/-- Budget-threaded `[LibsignalPlacement]` hook bundle over `A : RustCliAllocBudget M` and
`lim : BudgetLimits`. -/
structure RunHooksPlaced [LibsignalPlacement] (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : AllocContractsXCliPlaced A lim H
  allocFs : AllocContractsFsPlaced A lim H
  codec : CodecHooksPlaced M A lim H
  ser : SerContractsXPlaced M A lim H
  shim : HookSat H lsRustNoAllocShimSymCli (withVmPreserved noAllocShimSpec)
  shimVm : HookSat H lsRustNoAllocShimSymCli rustAllocShimVmSpec
  rawAlloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false)
  rawDealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim)
  framelessMemcpy : HookSat H memcpyName (withVmPreserved framelessMemcpySpec)
  sessionMemcpyRegion : HookSat H memcpyName sessionMemcpyRegionBudgetSpec
  memcpyRegionKeepsFs : HookSat H memcpyName sessionMemcpyRegionBudgetSpec.keepsFs
  memsetRegionKeepsFs : HookSat H memsetName sessionMemsetRegionBudgetSpec.keepsFs
  allocMemcpyVm : HookSat H memcpyName allocMemcpyVmSpec
  memcpyRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec)
  bcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec)
  e2eBcmp : HookSat H bcmpName (withVmPreserved e2eBcmpSpec)
  allocZeroed : HookSat H lsRustAllocZeroedSymCli (rustCliAllocBudgetSpec M A lim true)
  stringClone : HookSat H lsStringCloneSym (stringCloneBudgetSpec M A lim)
  formatInner : HookSat H lsFormatInnerSym (formatInnerBudgetSpec M A lim)
  pubFromSecret : HookSat H lsPubFromSecretSym (withVmPreserved (derivePublicKeyBytesSpec W.C.pubKey))
  dh : HookSat H lsDiffieHellmanSym (withVmPreserved (diffieHellmanSpec W.C.X))
  sharedDrop : HookSat H lsSharedSecretDropSym (withVmPreserved zeroizeSecretSpec)
  staticDrop : HookSat H lsStaticSecretDropSym (withVmPreserved zeroizeSecretSpec)
  blackBox : H lsBlackBoxSym = some blackBoxHook
  hkdf : HkdfPlacedHooksExactSat W.C.F H
  kemEncaps : H lsKemEncapsSym = some (kemEncapsHook W.Q.encaps)
  durationSince : H lsDurationSinceSym = some durationSinceExactHook
  panic_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked
  panic_raw : H "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked
  panic_sym : ∀ s, s ∈ cliPanicSymbolsPlaced → H s = some Rust.panicked
  fs : ∀ {prog : Program} {i : Nat} [IsLsBlockProg prog i H], TraceFsSound prog

/-! ## Constructor and downstream callee projections -/

/-- Constructs `RunHooksPlaced W A lim (cliGhostExterns g (cliExternsPlaced mmpl W))` from
`CliGhostSpqrAllocHooks` (providing `HkdfPlacedHooksExactSat`, `allocMemcpyVm`, and
`sessionMem{cpy,set}RegionBudgetSpec.keepsFs`) and `HookSat` witnesses for `String::clone` and `format_inner`. -/
theorem RunHooksPlaced.of_hooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetSpec M A lim)) :
    RunHooksPlaced W A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) := {
  alloc := allocContractsXCliPlaced_of_hooks mmpl g W hG.toCliGhostAllocHooks
  allocFs := allocContractsFsPlaced_of_hooks mmpl g W hG.toCliGhostAllocHooks
  codec := codecHooksPlaced_of_hooks mmpl g W hG.toCliGhostAllocHooks
  ser := serContractsXPlaced_of_hooks mmpl g W hG.toCliGhostAllocHooks
  shim := cliExternsPlaced_noAllocShim_budget_sat mmpl g W hG.shim_eq
  shimVm := cliExternsPlaced_rustAllocShimVm_sat mmpl g W hG.shim_eq
  rawAlloc := cliExternsPlaced_alloc_budget_sat mmpl g W hG.toCliGhostAllocHooks
  rawDealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hG.toCliGhostAllocHooks
  framelessMemcpy := cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hG.toCliGhostAllocHooks
  sessionMemcpyRegion :=
    cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG.toCliGhostAllocHooks
  memcpyRegionKeepsFs := by
    obtain ⟨f, hf, _, _, _, hReg, _, _, hVm, hFs, _⟩ := hG.memcpy
    exact ⟨f, cliGhostExterns_memcpy_some g _ hf, (hookOk_withVmPreserved hReg hVm).keepsFs hFs⟩
  memsetRegionKeepsFs := by
    obtain ⟨f, hf, _, _, _, hReg, hVm, hFs, _⟩ := hG.memset
    exact ⟨f, cliGhostExterns_memset_some g _ hf, (hookOk_withVmPreserved hReg hVm).keepsFs hFs⟩
  allocMemcpyVm := cliExternsPlaced_allocMemcpyVm_budget_sat mmpl g W hG.toCliGhostAllocHooks
  memcpyRO := cliExternsPlaced_memcpyRegionRO_budget_sat mmpl g W hG.toCliGhostAllocHooks
  bcmp := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
    (cliExternsPlaced_bcmp_budget_sat mmpl W)
  e2eBcmp := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
    (cliExternsPlaced_e2eBcmp_budget_sat mmpl W)
  allocZeroed := ⟨g.allocZeroed, cliGhostExterns_allocZeroed g _, hG.allocZeroed⟩
  stringClone := hStrClone
  formatInner := hFmtInner
  pubFromSecret := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
    (cliExternsPlaced_derivePublicKeyBytes_budget_sat mmpl W)
  dh := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
    (cliExternsPlaced_diffieHellman_budget_sat mmpl W)
  sharedDrop := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
    (cliExternsPlaced_sharedSecretDrop_budget_sat mmpl W)
  staticDrop := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
    (cliExternsPlaced_staticSecretDrop_budget_sat mmpl W)
  blackBox := (cliGhostExterns_other g _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans
    (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W))
  hkdf := HkdfPlacedHooksExactSat.of_allocHooks hG.toCliGhostAllocHooks
  kemEncaps := (cliGhostExterns_other g _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans
    (cliExternsPlaced_row mmpl W (kemEncaps_row_placed mmpl W))
  durationSince := (cliGhostExterns_other g _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans
    (cliExternsPlaced_row mmpl W (durationSince_row_placed mmpl W))
  panic_alloc := cliGhostExterns_panic_handle_alloc_error mmpl g W
  panic_raw := cliGhostExterns_panic_handle_error mmpl g W
  panic_sym := cliGhostExterns_panic_all mmpl g W
  fs := traceFsSound_cliGhostPlaced mmpl g W
    ⟨hG.alloc_fsT, hG.dealloc_fsT, hG.realloc_fsT, hG.allocZeroed_fsT,
     hG.shim_eq ▸ hookNoop_fsT, hStrFsT,
     by
       obtain ⟨f₀, hf₀, _, _, _, _, _, _, hfsT⟩ := hG.memset
       intro f hf; cases hf₀.symm.trans hf; exact hfsT,
     by
       obtain ⟨f₀, hf₀, _, _, _, _, _, _, _, _, hfsT⟩ := hG.memcpy
       intro f hf; cases hf₀.symm.trans hf; exact hfsT⟩
}

theorem RunHooksPlaced.sessionShim [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) :
    HookSat H lsRustNoAllocShimSymCli sessionShimBudgetSpec :=
  hookSat_sessionShimBudget_of_withVmPreserved hh.shim

theorem RunHooksPlaced.rawRealloc [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) :
    HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim) :=
  hh.codec.realloc

theorem RunHooksPlaced.toSkeletonRunHooksPlaced [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H)
    (hUtf8 : ∀ stk : Nat, HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec stk)))
    (hMemrchr : ∀ stk : Nat, HookSat H lsMemrchrSym (withVmPreserved (memrchrSpec stk))) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim H where
  alloc := hh.alloc
  allocFs := hh.allocFs
  panics := hh.panic_sym
  memcpyRO := hh.memcpyRO
  bcmp := hh.bcmp
  fs := fun _ _ => hh.fs
  utf8 := hUtf8
  memrchr := hMemrchr
  codecHooks := hh.codec
  allocZeroed := hh.allocZeroed
  stringClone := hh.stringClone
  formatInner := hh.formatInner

theorem RunHooksPlaced.portDepsPlaced [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) :
    PortDepsPlaced M A lim H :=
  portDepsPlaced_of_hooks hh.codec

theorem RunHooksPlaced.identityKeyPair_tryFrom_placed_ok [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) :
    subroutine_ok (lsProg_84 H) (blkPl_84).base (identityKeyPairTryFromPlacedSpec A lim) :=
  identityKeyPair_tryFrom_placed_ok_of_hooks hh.codec

theorem RunHooksPlaced.preKeyRecord_deserialize_placed_ok [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) :
    subroutine_ok (lsProg_65 H) (blkPl_65).base (preKeyDeserializePlacedSpec A lim) :=
  preKeyRecord_deserialize_placed_ok_of_hooks hh.codec

theorem RunHooksPlaced.identityKey_decode_placed_ok [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_hh : RunHooksPlaced W A lim H) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedSpec A) :=
  identityKey_decode_placed_ok_of_hooks H

theorem RunHooksPlaced.encodeRaw_placed_ok [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) :
    EncodeRawPlacedOkX M A lim H :=
  encodeRaw_placed_ok_of_serContractsX hh.ser

theorem RunHooksPlaced.encodeRaw_placed_cl [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hh : RunHooksPlaced W A lim H) :
    subroutine_ok callerProg (lsmpl.base 14) (withLsCl lsmpl (encodeRawSpecX M A lim)) :=
  encodeRaw_placed_cl_of_serContractsX hh.ser

theorem RunHooksPlaced.serialize_placed_ext_of_clone [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) (hClone : SessionClonePlacedOkX M A lim H) :
    SerializePlacedOkX M A lim H :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.serialize_placed_ext_of_clone
    hh.ser hClone

theorem RunHooksPlaced.serialize_placed_cl_of_clone [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hh : RunHooksPlaced W A lim H) (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52) (withLsCl lsmpl (serializeSpecX M A lim)) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.serialize_placed_cl_of_clone
    hh.ser hClone

theorem RunHooksPlaced.hSerEnv_placed_ext_of_clone [LibsignalPlacement] {W : CliHooks}
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) (hClone : SessionClonePlacedOkX M A lim H)
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (recordSerializeEnvSpecX Env M A lim)) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.hSerEnv_placed_ext_of_clone
    hh.ser hClone hsub

theorem RunHooksPlaced.hSerEnv_placed_cl_of_clone [LibsignalPlacement] {W : CliHooks}
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hh : RunHooksPlaced W A lim H) (hClone : SessionClonePlacedOkX M A lim H)
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeEnvSpecX Env M A lim)) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.hSerEnv_placed_cl_of_clone
    hh.ser hClone hsub

theorem RunHooksPlaced.hSer_placed_ext_of_clone [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (recordSerializeSpecX M A lim)) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.hSer_placed_ext_of_clone
    hh.ser hClone

theorem RunHooksPlaced.hSer_placed_cl_of_clone [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hh : RunHooksPlaced W A lim H) (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeSpecX M A lim)) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.hSer_placed_cl_of_clone
    hh.ser hClone

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
