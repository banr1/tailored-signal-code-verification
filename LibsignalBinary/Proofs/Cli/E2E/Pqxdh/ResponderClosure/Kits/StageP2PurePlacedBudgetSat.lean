/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat -- proof-setup: allow-public-import

/-!
# `HookSat` Sibling of `StageP2PurePlacedBudget` (`Kits/StageP2PurePlacedBudgetSat.lean`)

Provides the 20 closed `[LibsignalFullPlacement]` `initialize_bob_session` (Block `75`)
bridges on `stageP1ProgPlaced ext` from Section 6 of `StageP2PurePlacedBudget` re-typed over
`PqxdhPlacedHookContractsSat` (replacing `HkdfPlacedHooks`'s `memset` equality with
`HookSat ext lsMemsetSym sessionMemsetRegionBudgetSpec`).
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudgetSat

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalFrozen LibsignalFullPlacement
   lsMemcpySym lsProg_75 lsmpl)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.E2E.Pqxdh.Initiator
  (AcceptKeysInput Bytes Primitives StructuralPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto ls_subroutine_ok_withLsFrozen_of_block)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (stageP1ProgPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (PqxdhPlacedHookContractsSat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget (InitBobSessionBuildEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
  (initializeBobSessionErrFrozenPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
  (initializeBobSessionErrOwnedFrozenPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudgetSat
  (initializeBobSession_err_full_placed_ok_sat
   initializeBobSession_err_full_placed_ok_std_sat
   initializeBobSession_err_owned_full_placed_ok_sat
   initializeBobSession_err_owned_full_placed_ok_std_sat)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
  (InitBobV1EnvOfEnv InitialStateMemInvPlacedOk InitialStateMemInvPlacedOkOfEnv
   bobSpqrGhost initialStateFrozenPlacedOkOfEnv_of_codeRoLoaded)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudgetSat
  (initializeBobSession_ok_v1_full_placed_of_env_of_session_sat
   initializeBobSession_ok_v1_full_placed_of_env_std_sat)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
  (InitializeBobV1FrozenOkPlaced4KOfEnv InitializeBobV1FrozenOkPlacedOfEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
  (of_stageP2Defs_errOwned4K_frozen_placed)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
  (InitializeBobV1OptFieldsEnv ls_sepWPp_of_block
   p2_errOwned_frozen_to_defs4K_placed p2_initBobV1FrozenPlacedOfEnv_to_4K)

/-- Closed `[LibsignalFullPlacement]` rejecting run of `initialize_bob_session`
(`lsmpl.base 75`, `withLsCodeRoLoaded lsmpl (initializeBobSessionErrFrozenPlacedSpec ...)`)
on `stageP1ProgPlaced ext` under `PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_err_full_placed_ok_on_stageP1_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (withLsCodeRoLoaded lsmpl
        (initializeBobSessionErrFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P))) := by
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (initializeBobSession_err_full_placed_ok_sat hWF hP hH h_memcpy)
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_err_full_placed_ok_on_stageP1_sat`. -/
public theorem initializeBobSession_err_full_placed_ok_on_stageP1_std_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (withLsCodeRoLoaded lsmpl
        (initializeBobSessionErrFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P))) := by
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (initializeBobSession_err_full_placed_ok_std_sat hWF hP hH h_memcpy)
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-- Closed `[LibsignalFullPlacement]` owned-error rejecting run of `initialize_bob_session`
(`lsmpl.base 75`, `withLsCodeRoLoaded lsmpl (initializeBobSessionErrOwnedFrozenPlacedSpec ...)`)
on `stageP1ProgPlaced ext` under `PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_err_owned_full_placed_ok_on_stageP1_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (withLsCodeRoLoaded lsmpl
        (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P))) := by
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (initializeBobSession_err_owned_full_placed_ok_sat hWF hP hH h_memcpy)
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_err_owned_full_placed_ok_on_stageP1_sat`. -/
public theorem initializeBobSession_err_owned_full_placed_ok_on_stageP1_std_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (withLsCodeRoLoaded lsmpl
        (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P))) := by
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (initializeBobSession_err_owned_full_placed_ok_std_sat hWF hP hH h_memcpy)
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` owned-error rejecting run of `initialize_bob_session`
(`lsmpl.base 75`, `StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec`) on
`stageP1ProgPlaced ext` under `PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_err_owned_4k_defs_full_placed_ok_on_stageP1_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec
        P A lim (AcceptOptFieldsEnv P)) :=
  p2_errOwned_frozen_to_defs4K_placed
    (initializeBobSession_err_owned_full_placed_ok_on_stageP1_sat hWF hP hH h_memcpy)

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_err_owned_4k_defs_full_placed_ok_on_stageP1_sat`. -/
public theorem initializeBobSession_err_owned_4k_defs_full_placed_ok_on_stageP1_std_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec
        P A lim (AcceptOptFieldsEnv P)) :=
  p2_errOwned_frozen_to_defs4K_placed
    (initializeBobSession_err_owned_full_placed_ok_on_stageP1_std_sat hWF hP hH h_memcpy)

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` owned-error rejecting run of `initialize_bob_session`
(`lsmpl.base 75`, `Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec`) on
`stageP1ProgPlaced ext` under `PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_err_owned_4k_full_placed_ok_on_stageP1_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec
        P A lim (AcceptOptFieldsEnv P)) :=
  of_stageP2Defs_errOwned4K_frozen_placed
    (initializeBobSession_err_owned_4k_defs_full_placed_ok_on_stageP1_sat hWF hP hH h_memcpy)

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_err_owned_4k_full_placed_ok_on_stageP1_sat`. -/
public theorem initializeBobSession_err_owned_4k_full_placed_ok_on_stageP1_std_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec
        P A lim (AcceptOptFieldsEnv P)) :=
  of_stageP2Defs_errOwned4K_frozen_placed
    (initializeBobSession_err_owned_4k_defs_full_placed_ok_on_stageP1_std_sat hWF hP hH h_memcpy)

/-- Closed `[LibsignalFullPlacement]` envelope-parametric SPQR V1 `initialize_bob_session` success
(`InitializeBobV1FrozenOkPlacedOfEnv`) on `stageP1ProgPlaced ext` under `PqxdhPlacedHookContractsSat`,
taking only the `spqr::initial_state` seam (`LibsignalFrozen`). -/
public theorem initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_of_frozenInit_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  have hinit_fun : InitEnv (bobSpqrGhost s0.sp drKey.pqrKey) = BobInitEnv drKey.pqrKey :=
    funext fun evs => propext (hinit_eq s0.sp drKey.pqrKey evs)
  have henv_eq :
      InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey =
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) := by
    unfold InitBobV1EnvOfEnv; rw [hinit_fun]
  have hfits' :
      FitsEnv M lim st (InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey) :=
    henv_eq ▸ hfits
  have h75 := ls_sepWPp_of_block (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext)
    (i := 518) (j := 75) (LibsignalCodeLoaded.of_codeLoaded hfr.2)
    (initializeBobSession_ok_v1_full_placed_of_env_of_session_sat (Qp := Qp)
      hWF hP hH hMemcpy hinit s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
      ratchetKeyPairPtr outPtr drKey Frame hfr hfits' hrun hpc hsp hpqr
      hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)
    (by decide) (by decide) (by decide)
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs,
    localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
    ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
    hevs, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩ | hpan⟩ := h75 R hm hL
  · have hevs' :
        SeqEnv (AcceptOptFieldsEnv P inp)
          (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) evs :=
      henv_eq ▸ hevs
    exact ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hevs',
      localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

/-- Closed `[LibsignalFullPlacement]` envelope-parametric SPQR V1 `initialize_bob_session` success
on `stageP1ProgPlaced ext` taking `InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl)`
under `PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext :=
  initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_of_frozenInit_sat
    hWF hP hH hMemcpy (initialStateFrozenPlacedOkOfEnv_of_codeRoLoaded hinit) hinit_eq

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` envelope-parametric SPQR V1 `initialize_bob_session`
success on `stageP1ProgPlaced ext` under `PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_ok_v1_4k_full_placed_of_env_on_stageP1_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_sat
      hWF hP hH hMemcpy hinit hinit_eq)

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` envelope-parametric SPQR V1 `initialize_bob_session`
success on `stageP1ProgPlaced ext` taking `LibsignalFrozen` `hinit` under
`PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_ok_v1_4k_full_placed_of_env_on_stageP1_of_frozenInit_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_of_frozenInit_sat
      hWF hP hH hMemcpy hinit hinit_eq)

/-- `allocMemcpyVmSpec` variant of `initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_sat`. -/
public theorem initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_std_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  have hinit_fun : InitEnv (bobSpqrGhost s0.sp drKey.pqrKey) = BobInitEnv drKey.pqrKey :=
    funext fun evs => propext (hinit_eq s0.sp drKey.pqrKey evs)
  have henv_eq :
      InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey =
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) := by
    unfold InitBobV1EnvOfEnv; rw [hinit_fun]
  have hfits' :
      FitsEnv M lim st (InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey) :=
    henv_eq ▸ hfits
  have h75 := ls_sepWPp_of_block (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext)
    (i := 518) (j := 75) (LibsignalCodeLoaded.of_codeLoaded hfr.2)
    (initializeBobSession_ok_v1_full_placed_of_env_std_sat (Qp := Qp)
      hWF hP hH hMemcpy (initialStateFrozenPlacedOkOfEnv_of_codeRoLoaded hinit)
      s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
      ratchetKeyPairPtr outPtr drKey Frame hfr hfits' hrun hpc hsp hpqr
      hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)
    (by decide) (by decide) (by decide)
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs,
    localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
    ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
    hevs, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩ | hpan⟩ := h75 R hm hL
  · have hevs' :
        SeqEnv (AcceptOptFieldsEnv P inp)
          (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) evs :=
      henv_eq ▸ hevs
    exact ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hevs',
      localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

/-- `allocMemcpyVmSpec` variant of `initializeBobSession_ok_v1_4k_full_placed_of_env_on_stageP1_sat`. -/
public theorem initializeBobSession_ok_v1_4k_full_placed_of_env_on_stageP1_std_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_std_sat
      hWF hP hH hMemcpy hinit hinit_eq)

/-- Closed `[LibsignalFullPlacement]` SPQR V1 `initialize_bob_session` success at
`InitializeBobV1OptFieldsEnv P F` on `stageP1ProgPlaced ext` (`sessionMemcpyRegionBudgetSpec`)
under `PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_ok_v1_full_placed_on_stageP1_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_sat
    hWF hP hH hMemcpy hinit (fun _ _ _ => Iff.rfl)

/-- Closed `[LibsignalFullPlacement]` SPQR V1 `initialize_bob_session` success at
`InitializeBobV1OptFieldsEnv P F` on `stageP1ProgPlaced ext` taking `LibsignalFrozen` `hinit`
under `PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_ok_v1_full_placed_on_stageP1_of_frozenInit_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalFrozen lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_of_frozenInit_sat
    hWF hP hH hMemcpy hinit (fun _ _ _ => Iff.rfl)

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` SPQR V1 `initialize_bob_session` success at
`InitializeBobV1OptFieldsEnv P F` on `stageP1ProgPlaced ext` (`sessionMemcpyRegionBudgetSpec`)
under `PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_ok_v1_4k_full_placed_on_stageP1_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_on_stageP1_sat hWF hP hH hMemcpy hinit)

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` SPQR V1 `initialize_bob_session` success at
`InitializeBobV1OptFieldsEnv P F` on `stageP1ProgPlaced ext` taking `LibsignalFrozen` `hinit`
under `PqxdhPlacedHookContractsSat`. -/
public theorem initializeBobSession_ok_v1_4k_full_placed_on_stageP1_of_frozenInit_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalFrozen lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_on_stageP1_of_frozenInit_sat hWF hP hH hMemcpy hinit)

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_ok_v1_full_placed_on_stageP1_sat`. -/
public theorem initializeBobSession_ok_v1_full_placed_on_stageP1_std_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_std_sat
    hWF hP hH hMemcpy hinit (fun _ _ _ => Iff.rfl)

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_ok_v1_4k_full_placed_on_stageP1_sat`. -/
public theorem initializeBobSession_ok_v1_4k_full_placed_on_stageP1_std_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_on_stageP1_std_sat hWF hP hH hMemcpy hinit)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudgetSat
