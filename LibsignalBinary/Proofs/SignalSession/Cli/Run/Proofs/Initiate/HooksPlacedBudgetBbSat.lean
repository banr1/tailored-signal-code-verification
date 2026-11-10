/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `HookSat` `black_box` Sibling of Budget `Initiate.HooksPlacedBudget` (`HooksPlacedBudgetBbSat`)

Stacks `blackBox : HookSat H lsBlackBoxSym blackBoxSpecSat` on top of post-WP6b
`HooksPlacedBudget.RunHooksPlaced` (`hkdf : HkdfPlacedHooksExactSat W.C.F H`,
`memcpyRegionKeepsFs`, `memsetRegionKeepsFs`):
- `RunHooksPlacedBbSat`
- `RunHooksPlaced.toBbSat`
- `RunHooksPlacedBbSat.of_hooks_bb_sat` (taking `hG` and `hBb`, with zero reference to
  `blackBox_row_placed`) and `RunHooksPlacedBbSat.of_hooks`
- All 14 downstream callee/bundle projections matching `HooksPlacedBudget`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudgetBbSat

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.E2E (bcmpName kemEncapsHook)
open CryptoVerification.E2E.HooksE (e2eBcmpSpec)
open CryptoVerification.E2E.Record.Placed (blkPl_52 lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit (TraceFsSound)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet
  (derivePublicKeyBytesSpec diffieHellmanSpec framelessMemcpySpec memcpyName memsetName
   noAllocShimSpec zeroizeSecretSpec)
open CryptoVerification.RecordCodecs.Placed (blkPl_18 blkPl_65 blkPl_84 lsProg_18 lsProg_65 lsProg_84)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced cliPanicSymbolsPlaced durationSinceExactHook lsBlackBoxSym
   lsDiffieHellmanSym lsDurationSinceSym lsFormatInnerSym lsFromUtf8Sym lsMemrchrSym
   lsPubFromSecretSym lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli
   lsRustNoAllocShimSymCli lsRustReallocSymCli lsSharedSecretDropSym lsStaticSecretDropSym
   lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (cliBcmpName cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.MainHops (fromUtf8AsciiSpec memrchrSpec)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks IsFsC cliExternsPlaced_row cliGhostExterns cliGhostExterns_allocZeroed
   cliGhostExterns_memcpy_some cliGhostExterns_memset_some cliGhostExterns_other hookNoop_fsT)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (lsKemEncapsSym traceFsSound_cliGhostPlaced)
open CryptoVerification.SignalSession.Cli.Slots
  (blackBox_row_placed cliGhostExterns_panic_all cliGhostExterns_panic_handle_alloc_error
   cliGhostExterns_panic_handle_error cliGhostExterns_sat_of_cliExternsPlaced
   durationSince_row_placed kemEncaps_row_placed)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpec
   rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (allocMemcpyVmSpec rustAllocShimVmSpec stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (formatInnerBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat hookSat_blackBox_of_eq)
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
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced cliExternsPlaced_rustAllocShimVm_sat serContractsXPlaced_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostSpqrAllocHooks allocContractsFsPlaced_of_hooks allocContractsXCliPlaced_of_hooks
   cliExternsPlaced_allocMemcpyVm_budget_sat cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_bcmp_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_derivePublicKeyBytes_budget_sat cliExternsPlaced_diffieHellman_budget_sat
   cliExternsPlaced_e2eBcmp_budget_sat cliExternsPlaced_framelessMemcpy_budget_sat
   cliExternsPlaced_memcpyRegionRO_budget_sat cliExternsPlaced_noAllocShim_budget_sat
   cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemsetRegion_budget_sat
   cliExternsPlaced_sharedSecretDrop_budget_sat cliExternsPlaced_staticSecretDrop_budget_sat
   codecHooksPlaced_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)

/-- `HookSat`-backed `black_box` sibling stacked on `HooksPlacedBudget.RunHooksPlaced`
(`hkdf : HkdfPlacedHooksExactSat W.C.F H`, `memcpyRegionKeepsFs`, `memsetRegionKeepsFs`). -/
structure RunHooksPlacedBbSat [LibsignalPlacement] (W : CliHooks) {M : AllocCostModel}
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
  blackBox : HookSat H lsBlackBoxSym blackBoxSpecSat
  hkdf : HkdfPlacedHooksExactSat W.C.F H
  kemEncaps : H lsKemEncapsSym = some (kemEncapsHook W.Q.encaps)
  durationSince : H lsDurationSinceSym = some durationSinceExactHook
  panic_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked
  panic_raw : H "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked
  panic_sym : ∀ s, s ∈ cliPanicSymbolsPlaced → H s = some Rust.panicked
  fs : ∀ {prog : Program} {i : Nat} [IsLsBlockProg prog i H], TraceFsSound prog

/-- Coercion `HooksPlacedBudget.RunHooksPlaced → RunHooksPlacedBbSat` (weakening only `blackBox`). -/
theorem RunHooksPlaced.toBbSat [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : RunHooksPlaced W A lim H) :
    RunHooksPlacedBbSat W A lim H where
  alloc := h.alloc
  allocFs := h.allocFs
  codec := h.codec
  ser := h.ser
  shim := h.shim
  shimVm := h.shimVm
  rawAlloc := h.rawAlloc
  rawDealloc := h.rawDealloc
  framelessMemcpy := h.framelessMemcpy
  sessionMemcpyRegion := h.sessionMemcpyRegion
  memcpyRegionKeepsFs := h.memcpyRegionKeepsFs
  memsetRegionKeepsFs := h.memsetRegionKeepsFs
  allocMemcpyVm := h.allocMemcpyVm
  memcpyRO := h.memcpyRO
  bcmp := h.bcmp
  e2eBcmp := h.e2eBcmp
  allocZeroed := h.allocZeroed
  stringClone := h.stringClone
  formatInner := h.formatInner
  pubFromSecret := h.pubFromSecret
  dh := h.dh
  sharedDrop := h.sharedDrop
  staticDrop := h.staticDrop
  blackBox := hookSat_blackBox_of_eq h.blackBox
  hkdf := h.hkdf
  kemEncaps := h.kemEncaps
  durationSince := h.durationSince
  panic_alloc := h.panic_alloc
  panic_raw := h.panic_raw
  panic_sym := h.panic_sym
  fs := h.fs

/-- Construct `RunHooksPlacedBbSat W A lim (cliGhostExterns g (cliExternsPlaced mmpl W))` from
`CliGhostSpqrAllocHooks M A lim g`, `hBb`, and `HookSat` witnesses for `String::clone`
and `format_inner` (with zero reference to `blackBox_row_placed`). -/
theorem RunHooksPlacedBbSat.of_hooks_bb_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (hBb : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsBlackBoxSym
      blackBoxSpecSat)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetSpec M A lim)) :
    RunHooksPlacedBbSat W A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) where
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
    rcases cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG.toCliGhostAllocHooks with
      ⟨f, hf, hok⟩
    obtain ⟨f₀, hf₀, _, _, _, _, _, _, _, hfs₀, _⟩ := hG.memcpy
    cases (cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hf₀).symm.trans hf
    exact ⟨f, hf, hok.keepsFs hfs₀⟩
  memsetRegionKeepsFs := by
    rcases cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG.toCliGhostAllocHooks with
      ⟨f, hf, hok⟩
    obtain ⟨f₀, hf₀, _, _, _, _, _, hfs₀, _⟩ := hG.memset
    cases (cliGhostExterns_memset_some g (cliExternsPlaced mmpl W) hf₀).symm.trans hf
    exact ⟨f, hf, hok.keepsFs hfs₀⟩
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
  blackBox := hBb
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

/-- Construct `RunHooksPlacedBbSat W A lim (cliGhostExterns g (cliExternsPlaced mmpl W))` from
`CliGhostSpqrAllocHooks M A lim g` and `HookSat` witnesses for `String::clone` and `format_inner`. -/
theorem RunHooksPlacedBbSat.of_hooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetSpec M A lim)) :
    RunHooksPlacedBbSat W A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  RunHooksPlacedBbSat.of_hooks_bb_sat mmpl g W hG
    (hookSat_blackBox_of_eq
      ((cliGhostExterns_other g _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W))))
    hStrFsT hStrClone hFmtInner

/-- Project `sessionShimBudgetSpec` out of `RunHooksPlacedBbSat.shim`. -/
theorem RunHooksPlacedBbSat.sessionShim [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlacedBbSat W A lim H) :
    HookSat H lsRustNoAllocShimSymCli sessionShimBudgetSpec :=
  hookSat_sessionShimBudget_of_withVmPreserved hh.shim

/-- Project `rawRealloc` (`rustCliReallocBudgetSpec M A lim`) out of `RunHooksPlacedBbSat.codec`. -/
theorem RunHooksPlacedBbSat.rawRealloc [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlacedBbSat W A lim H) :
    HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim) :=
  hh.codec.realloc

/-- Project `SkeletonPlacedBudget.RunHooksPlaced` given `utf8` and `memrchr` hooks. -/
theorem RunHooksPlacedBbSat.toSkeletonRunHooksPlaced [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlacedBbSat W A lim H)
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

/-- Project `PortDepsPlaced M A lim H` (`RecordCodecs.AssemblyBudget`, incl. E4PORT) from
`RunHooksPlacedBbSat`. -/
theorem RunHooksPlacedBbSat.portDepsPlaced [LibsignalPlacement] {W : CliHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlacedBbSat W A lim H) :
    PortDepsPlaced M A lim H :=
  portDepsPlaced_of_hooks hh.codec

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (Block `84`) from `RunHooksPlacedBbSat`. -/
theorem RunHooksPlacedBbSat.identityKeyPair_tryFrom_placed_ok [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlacedBbSat W A lim H) :
    subroutine_ok (lsProg_84 H) (blkPl_84).base (identityKeyPairTryFromPlacedSpec A lim) :=
  identityKeyPair_tryFrom_placed_ok_of_hooks hh.codec

/-- `PreKeyRecord::deserialize` (Block `65`) from `RunHooksPlacedBbSat`. -/
theorem RunHooksPlacedBbSat.preKeyRecord_deserialize_placed_ok [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlacedBbSat W A lim H) :
    subroutine_ok (lsProg_65 H) (blkPl_65).base (preKeyDeserializePlacedSpec A lim) :=
  preKeyRecord_deserialize_placed_ok_of_hooks hh.codec

/-- `IdentityKey::decode` (Block `18`) over `A : RustCliAllocBudget M` from `RunHooksPlacedBbSat`. -/
theorem RunHooksPlacedBbSat.identityKey_decode_placed_ok [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_hh : RunHooksPlacedBbSat W A lim H) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedSpec A) :=
  identityKey_decode_placed_ok_of_hooks H

/-- `encodeRaw` (Block `14`) from `RunHooksPlacedBbSat`. -/
theorem RunHooksPlacedBbSat.encodeRaw_placed_ok [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlacedBbSat W A lim H) :
    EncodeRawPlacedOkX M A lim H :=
  encodeRaw_placed_ok_of_serContractsX hh.ser

/-- Caller-block-polymorphic `encodeRaw` (Block `14`) from `RunHooksPlacedBbSat`. -/
theorem RunHooksPlacedBbSat.encodeRaw_placed_cl [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hh : RunHooksPlacedBbSat W A lim H) :
    subroutine_ok callerProg (lsmpl.base 14) (withLsCl lsmpl (encodeRawSpecX M A lim)) :=
  encodeRaw_placed_cl_of_serContractsX hh.ser

/-- `SessionRecord::serialize` (`serializeSpecX`, Block `52`) from `RunHooksPlacedBbSat` and
`SessionClonePlacedOkX`. -/
theorem RunHooksPlacedBbSat.serialize_placed_ext_of_clone [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlacedBbSat W A lim H) (hClone : SessionClonePlacedOkX M A lim H) :
    SerializePlacedOkX M A lim H :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.serialize_placed_ext_of_clone
    hh.ser hClone

/-- Caller-block-polymorphic `SessionRecord::serialize` (`serializeSpecX`, Block `52`) from
`RunHooksPlacedBbSat` and `SessionClonePlacedOkX`. -/
theorem RunHooksPlacedBbSat.serialize_placed_cl_of_clone [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hh : RunHooksPlacedBbSat W A lim H) (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52) (withLsCl lsmpl (serializeSpecX M A lim)) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.serialize_placed_cl_of_clone
    hh.ser hClone

/-- Parametric-envelope `hSer` (`recordSerializeEnvSpecX`, Block `52`) from `RunHooksPlacedBbSat`
and `SessionClonePlacedOkX`. -/
theorem RunHooksPlacedBbSat.hSerEnv_placed_ext_of_clone [LibsignalPlacement] {W : CliHooks}
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlacedBbSat W A lim H) (hClone : SessionClonePlacedOkX M A lim H)
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (recordSerializeEnvSpecX Env M A lim)) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.hSerEnv_placed_ext_of_clone
    hh.ser hClone hsub

/-- Caller-block-polymorphic parametric-envelope `hSer` (`recordSerializeEnvSpecX`, Block `52`). -/
theorem RunHooksPlacedBbSat.hSerEnv_placed_cl_of_clone [LibsignalPlacement] {W : CliHooks}
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hh : RunHooksPlacedBbSat W A lim H) (hClone : SessionClonePlacedOkX M A lim H)
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeEnvSpecX Env M A lim)) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.hSerEnv_placed_cl_of_clone
    hh.ser hClone hsub

/-- Canonical-envelope (`SerializeEnvX`) `hSer` (`recordSerializeSpecX`, Block `52`) from
`RunHooksPlacedBbSat` and `SessionClonePlacedOkX`. -/
theorem RunHooksPlacedBbSat.hSer_placed_ext_of_clone [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlacedBbSat W A lim H) (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (recordSerializeSpecX M A lim)) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.hSer_placed_ext_of_clone
    hh.ser hClone

/-- Caller-block-polymorphic canonical-envelope (`SerializeEnvX`) `hSer` (`recordSerializeSpecX`,
Block `52`). -/
theorem RunHooksPlacedBbSat.hSer_placed_cl_of_clone [LibsignalPlacement] {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hh : RunHooksPlacedBbSat W A lim H) (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeSpecX M A lim)) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget.hSer_placed_cl_of_clone
    hh.ser hClone

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudgetBbSat
