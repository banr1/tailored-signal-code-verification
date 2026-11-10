/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlacedBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedBBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget

/-!
# `HookSat` Sibling of `ResponderCanonicalPlacedBudget` (`ResponderCanonicalPlacedBudgetSat`)

Provides the `[LibsignalFullPlacement]` `Pqxdh::accept` (Block `79`) corollaries of
`ResponderCanonicalPlacedBudget` Section 2 re-typed over
`ResponderPqxdhPlacedHookContractsSat` and `hMs`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudgetSat

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalFullPlacement LibsignalHooks lsMemcpySym lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.E2E.Pqxdh.Initiator (Primitives StructuralPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto ofSignalPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchet (lsMemsetSym)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliModelPrims_matchCrypto cliModelPrims_structural)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget
  (vecAppendElements_fast_placed_ok_cl)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
  (pqxdhAcceptOptFieldsFrozenPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedBBudget
  (pqxdhAccept_opt_fields_placed_ok_of_block)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlacedBudget
  (pqxdhAcceptErrOwnedFrozenPlacedSpec pqxdhAccept_err_owned_placed_ok_of_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_framelessMemcpy_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget
  (ecPubKeyIsCanonical_responder_placed_ok_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudgetSat
  (ResponderPqxdhPlacedHookContractsSat cliResponderPqxdhHookContractsPlaced_sat)

private theorem hookSat_framelessMemcpy_of_vm_local {H : LibsignalHooks}
    (h : HookSat H "memcpy"
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H lsMemcpySym framelessMemcpySpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpySpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

/-- Closed `[LibsignalFullPlacement]` budget-threaded contract for `Pqxdh::accept` (Block `79`)
from `ResponderPqxdhPlacedHookContractsSat` and `HookSat H lsMemcpySym framelessMemcpySpec`. -/
public theorem pqxdhAccept_opt_fields_responder_full_placed_ok_of_block_sat
    [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : ResponderPqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  pqxdhAccept_opt_fields_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_responder_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    (vecAppendElements_fast_placed_ok_cl h_memcpy)
    (hH.hkdfExtract_ok hP)
    (hH.hkdfExpandMultiInfo_ok hP)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy hH.kyberDecaps

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting contract for
`Pqxdh::accept` (Block `79`) from `ResponderPqxdhPlacedHookContractsSat`. -/
public theorem pqxdhAccept_err_owned_responder_full_placed_ok_of_block_sat
    [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : ResponderPqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  pqxdhAccept_err_owned_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_responder_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy

/-- Closed `[LibsignalFullPlacement]` `pqxdhAcceptOptFieldsFrozenPlacedSpec` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim gh` and `hMs`. -/
public theorem cliPqxdhAccept_opt_fields_full_placed_ok_sat [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hMs : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
        A lim
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))) :=
  pqxdhAccept_opt_fields_responder_full_placed_ok_of_block_sat
    (cliModelPrims_structural X W)
    (cliModelPrims_matchCrypto X W)
    (cliResponderPqxdhHookContractsPlaced_sat X mmpl gh W hG hMs)
    (hookSat_framelessMemcpy_of_vm_local
      (cliExternsPlaced_framelessMemcpy_budget_sat mmpl gh W hG))

/-- Closed `[LibsignalFullPlacement]` `pqxdhAcceptErrOwnedFrozenPlacedSpec` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim gh` and `hMs`. -/
public theorem cliPqxdhAccept_err_owned_full_placed_ok_sat [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hMs : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptErrOwnedFrozenPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
        A lim
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))) :=
  pqxdhAccept_err_owned_responder_full_placed_ok_of_block_sat
    (cliModelPrims_structural X W)
    (cliModelPrims_matchCrypto X W)
    (cliResponderPqxdhHookContractsPlaced_sat X mmpl gh W hG hMs)
    (hookSat_framelessMemcpy_of_vm_local
      (cliExternsPlaced_framelessMemcpy_budget_sat mmpl gh W hG))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudgetSat
