/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat

/-!
# `HookSat` Sibling of `Stage2V1BasePlacedBudget` (`Stage2V1BasePlacedBudgetSat`)

Provides `ResponderPqxdhPlacedHookContractsSat` (replacing `HkdfPlacedHooks C.F H` with
`HkdfPlacedHooksExactSat C.F H` and `HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`),
plain coercion `ResponderPqxdhPlacedHookContracts.toSat`, all 8 bundle projections, and the
`CliGhostAllocHooks`-parameterized CLI Poll `cliGhostExterns` instances.
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudgetSat

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement
   lsBlackBoxU8Sym lsRustDeallocSym lsRustNoAllocShimSym lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.E2E.Pqxdh.Initiator (Primitives StructuralPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto lsDalekMontToEdSym lsDalekTorsionFreeSym lsKyberDecapsSym
   ofSignalPqxdhPrimitives)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet
  (diffieHellmanSpec lsMemsetSym withLsCodeRoLoaded zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (lsDhSym lsRustAllocSym lsSharedDropSym lsStaticDropSym)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (cliModelPrims_matchCrypto)
open CryptoVerification.SignalSession.Cli.Slots
  (blackBox_row_placed cliGhostExterns_sat_of_cliExternsPlaced)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk
   handshakeKeysDerivePlacedBaseSpec handshakeKeysDerivePlacedVmSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
  (PqxdhCalculateAgreementPlacedFrozenOk PqxdhCalculateAgreementPlacedOk
   pqxdhCalculateAgreement_placed_frozen_ok_of_block pqxdhCalculateAgreement_placed_ok_of_block)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
  (cryptoBoolRegStubBudgetSpec kyberDecapsStubBudgetSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (createChain_placed_ok_of_block_sat createChain_placed_ok_x_of_block_sat
   handshakeKeysDerive_placed_ok_of_block_sat handshakeKeysDerive_placed_vm_ok_of_block_sat
   pqxdhHkdfExpandMultiInfo_placed_ok_sat pqxdhHkdfExtract_placed_ok_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_diffieHellman_budget_sat
   cliExternsPlaced_sharedSecretDrop_budget_sat cliExternsPlaced_staticSecretDrop_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
  (ResponderPqxdhPlacedHookContracts cliExternsPlaced_kemDecaps_budget_sat
   cliExternsPlaced_noAllocShimBudget_sat cliExternsPlaced_toEdwards_budget_sat
   cliExternsPlaced_torsionFree_budget_sat dalekMontToEdResponderBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (HkdfPlacedHooks.toBudgetSat HkdfPlacedHooks.toExactBudgetSat HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec createChainSpecX)

private theorem hookSat_noAllocShimBudget_of_withVmPreserved_local {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec,
      noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- `HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W))` from
`CliGhostAllocHooks M A lim g` and `HookSat … sessionMemsetRegionBudgetSpec`. -/
public theorem hkdfPlacedHooksBudgetSat_cli_poll [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  let _ := hMs
  exact HkdfPlacedHooksExactSat.of_allocHooks hG

/-- `HkdfPlacedHooksExactSat` at `cliGhostExterns` lifted from `HookSat` on `cliExternsPlaced`. -/
public theorem hkdfPlacedHooksBudgetSat_cli_poll_of_cliExternsPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliExternsPlaced mmpl W) lsMemsetSym sessionMemsetRegionBudgetSpec) :
    HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  let _ := hMs
  exact HkdfPlacedHooksExactSat.of_allocHooks hG

/-- Combined budget-threaded external-hook contract bundle for `ResponderCore` (`HookSat` sibling of
`ResponderPqxdhPlacedHookContracts`, replacing `HkdfPlacedHooks` with `HkdfPlacedHooksExactSat`
and `HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`). -/
public structure ResponderPqxdhPlacedHookContractsSat [LibsignalPlacement]
    (M : AllocCostModel) (P : Primitives) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooksExactSat C.F H
  memsetBudget     : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec
  dh               : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X))
  sharedDrop       : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec)
  staticDrop       : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)
  blackBox         : H lsBlackBoxU8Sym = some blackBoxHook
  noAllocShim      : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec
  alloc            : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc          : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubBudgetSpec P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym (dalekMontToEdResponderBudgetSpec P)
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubBudgetSpec P.isTorsionFree 160)

/-- Coerce `ResponderPqxdhPlacedHookContracts` into `ResponderPqxdhPlacedHookContractsSat`
(plain theorem, never an `instance`). -/
public theorem ResponderPqxdhPlacedHookContracts.toSat [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H) :
    ResponderPqxdhPlacedHookContractsSat M P C A lim H :=
  { hkdf := (HkdfPlacedHooks.toExactBudgetSat hH.hkdf).toExactSat
    memsetBudget := (HkdfPlacedHooks.toBudgetSat hH.hkdf).memset
    dh := hH.dh
    sharedDrop := hH.sharedDrop
    staticDrop := hH.staticDrop
    blackBox := hH.blackBox
    noAllocShim := hH.noAllocShim
    alloc := hH.alloc
    dealloc := hH.dealloc
    kyberDecaps := hH.kyberDecaps
    dalekMontToEd := hH.dalekMontToEd
    dalekTorsionFree := hH.dalekTorsionFree }

/-- Bundle projection: `PqxdhCalculateAgreementPlacedOk` on any caller block `i < 619`. -/
public theorem ResponderPqxdhPlacedHookContractsSat.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

/-- Bundle projection: `PqxdhCalculateAgreementPlacedFrozenOk` on any caller block `i < 619`. -/
public theorem ResponderPqxdhPlacedHookContractsSat.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

/-- Bundle projection: `HandshakeDeriveBudget.PqxdhHkdfExtractPlacedOk` on any caller block `i < 619`. -/
public theorem ResponderPqxdhPlacedHookContractsSat.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  exact pqxdhHkdfExtract_placed_ok_sat hP hi

/-- Bundle projection: `HandshakeDeriveBudget.PqxdhHkdfExpandMultiInfoPlacedOk` on any caller block
`i < 619`. -/
public theorem ResponderPqxdhPlacedHookContractsSat.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  exact pqxdhHkdfExpandMultiInfo_placed_ok_sat hP hi

/-- Bundle projection: `<HandshakeKeys>::derive` (`VmPreserved`, Block `59`) on any caller block
`i < 619`. -/
public theorem ResponderPqxdhPlacedHookContractsSat.handshakeKeysDerive_vm_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsSat M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedVmSpec P)) := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  exact handshakeKeysDerive_placed_vm_ok_of_block_sat hWF hP hi

/-- Bundle projection: `<HandshakeKeys>::derive` (`RustCliAllocBudget`, Block `59`) on any caller
block `i < 619`. -/
public theorem ResponderPqxdhPlacedHookContractsSat.handshakeKeysDerive_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsSat M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec M P A lim)) := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  exact handshakeKeysDerive_placed_ok_of_block_sat hWF hP hi

/-- Bundle projection: `<RootKey>::create_chain` (Block `40`) on any caller block `i < 619`. -/
public theorem ResponderPqxdhPlacedHookContractsSat.createChain_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsSat M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)) := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  exact createChain_placed_ok_of_block_sat hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.dealloc hi

/-- Bundle projection: `<RootKey>::create_chain` at `createChainStackX` (Block `40`) on any caller
block `i < 619`. -/
public theorem ResponderPqxdhPlacedHookContractsSat.createChain_x_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsSat M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)) := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  exact createChain_placed_ok_x_of_block_sat hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.dealloc hi

/-- `ResponderPqxdhPlacedHookContractsSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g`, `hMs`, and `HookSat` contracts for `alloc`, `dealloc`, and
`noAllocShim`. -/
public theorem cliResponderPqxdhHookContractsPlaced_of_hookSat_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq) :
    ResponderPqxdhPlacedHookContractsSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  { hkdf := hkdfPlacedHooksBudgetSat_cli_poll mmpl g W hG hMs
    memsetBudget := hMs
    dh := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_diffieHellman_budget_sat mmpl W)
    sharedDrop := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_sharedSecretDrop_budget_sat mmpl W)
    staticDrop := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_staticSecretDrop_budget_sat mmpl W)
    blackBox := (cliGhostExterns_other g (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W))
    noAllocShim := hnoAllocShim
    alloc := halloc
    dealloc := hdealloc
    kyberDecaps := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_kemDecaps_budget_sat mmpl W X)
    dalekMontToEd := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_toEdwards_budget_sat mmpl W X)
    dalekTorsionFree := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_torsionFree_budget_sat mmpl W X) }

/-- `ResponderPqxdhPlacedHookContractsSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g` and `hMs`. -/
public theorem cliResponderPqxdhHookContractsPlaced_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    ResponderPqxdhPlacedHookContractsSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_of_hookSat_sat X mmpl g W hG hMs
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq)

/-- `ResponderPqxdhPlacedHookContractsSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g`, `SkeletonPlacedBudget.RunHooksPlaced`, and `hMs`. -/
public theorem cliResponderPqxdhHookContractsPlaced_of_runHooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    ResponderPqxdhPlacedHookContractsSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_of_hookSat_sat X mmpl g W hG hMs
    hh.codecHooks.alloc hh.codecHooks.dealloc
    (hookSat_noAllocShimBudget_of_withVmPreserved_local hh.codecHooks.shim)

/-- `PqxdhHkdfExtractPlacedOk` (`HandshakeDeriveBudget`) on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g` and `hMs`. -/
public theorem cliPqxdhHkdfExtract_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) callerProg := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    hkdfPlacedHooksBudgetSat_cli_poll mmpl g W hG hMs
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hMs
  exact pqxdhHkdfExtract_placed_ok_sat
    (C := W.C) (H := cliGhostExterns g (cliExternsPlaced mmpl W))
    (cliModelPrims_matchCrypto X W) hi

/-- `PqxdhHkdfExpandMultiInfoPlacedOk` (`HandshakeDeriveBudget`) on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g` and `hMs`. -/
public theorem cliPqxdhHkdfExpandMultiInfo_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) callerProg := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    hkdfPlacedHooksBudgetSat_cli_poll mmpl g W hG hMs
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hMs
  exact pqxdhHkdfExpandMultiInfo_placed_ok_sat
    (C := W.C) (H := cliGhostExterns g (cliExternsPlaced mmpl W))
    (cliModelPrims_matchCrypto X W) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudgetSat
