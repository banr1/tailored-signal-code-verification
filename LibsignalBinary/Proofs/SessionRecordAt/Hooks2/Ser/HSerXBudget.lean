/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExtBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1ExtBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRawXBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyXBudget
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget

/-!
# Budget-Threaded `SessionRecord::serialize` Assembly (Block `52`)

Composes the budget-threaded Block `14` (`SessionStructure::encode_raw`), Block `6`
(`drop_glue::<SessionStructure>`), and Block `80` (`SessionClonePlacedOkX`) contracts to establish
`serializeSpecX`, `recordSerializeEnvSpecX`, and `recordSerializeSpecX` on Block `52`
(`SessionRecord::serialize`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl
)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52)
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.AdaptersBudget (Stage2ContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget (do_reserve_placed_ok_ext_x)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1ExtBudget (
  drop_session_structure_local1_placed_ok_ext
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerContractsXPlaced serContractsXPlaced_of_stage2ContractsPlaced
  SerializeEnvX encodeRawSpecX serializeSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  DoReservePlacedOkX EncodeVarintPlacedOkX
  EncodeRawPlacedOkX SessionClonePlacedOkX DropSessionStructureLocal1PlacedOkX
  SerializePlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRawXBudget (
  encodeRaw_placed_ok_of_contracts
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExtBudget (
  recordSerializeEnvSpecX recordSerializeSpecX
  recordSerializeEnv_placed_ok_ext_of_serializeX recordSerialize_placed_ok_ext_of_serializeX
  recordSerializeEnv_placed_cl_of_serializeX recordSerialize_placed_cl_of_serializeX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyXBudget (
  serialize_placed_ok_of_leaves_ext serialize_placed_cl_of_leaves_ext
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget (
  encode_varint_placed_ok_of_doReserve_x
)

/-- Relocatable `encodeRaw` contract (Block `14`) from `SerContractsXPlaced` alone. -/
theorem encodeRaw_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : SerContractsXPlaced M A lim H) :
    EncodeRawPlacedOkX M A lim H := by
  have hDR : DoReservePlacedOkX M A lim H := do_reserve_placed_ok_ext_x hC.alloc
  have hEV : EncodeVarintPlacedOkX M A lim H :=
    encode_varint_placed_ok_of_doReserve_x A lim H hDR
  exact encodeRaw_placed_ok_of_contracts A lim H hC hEV hDR

theorem encodeRaw_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 14) (withLsCl lsmpl (encodeRawSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeRaw_placed_ok_of_serContractsX hC)

/-- Relocatable `SessionRecord::serialize` (`serializeSpecX M A lim`, Block `52`) from
`SerContractsXPlaced` and `SessionClonePlacedOkX`. -/
theorem serialize_placed_ext_of_clone [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H) :
    SerializePlacedOkX M A lim H := by
  have hDR : DoReservePlacedOkX M A lim H := do_reserve_placed_ok_ext_x hC.alloc
  have hEV : EncodeVarintPlacedOkX M A lim H :=
    encode_varint_placed_ok_of_doReserve_x A lim H hDR
  have hRaw := encodeRaw_placed_ok_of_serContractsX hC
  have hDrop : DropSessionStructureLocal1PlacedOkX M A lim H :=
    drop_session_structure_local1_placed_ok_ext hC.alloc
  exact serialize_placed_ok_of_leaves_ext hC hClone hEV hRaw hDrop

theorem serialize_placed_cl_of_clone [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializeSpecX M A lim)) := by
  have hDR : DoReservePlacedOkX M A lim H := do_reserve_placed_ok_ext_x hC.alloc
  have hEV : EncodeVarintPlacedOkX M A lim H :=
    encode_varint_placed_ok_of_doReserve_x A lim H hDR
  have hRaw := encodeRaw_placed_ok_of_serContractsX hC
  have hDrop : DropSessionStructureLocal1PlacedOkX M A lim H :=
    drop_session_structure_local1_placed_ok_ext hC.alloc
  exact serialize_placed_cl_of_leaves_ext hC hClone hEV hRaw hDrop

/-- Parametric-envelope relocatable `SessionRecord::serialize` (Block `52`) from
`SerContractsXPlaced` and `SessionClonePlacedOkX` for any envelope `Env` containing
`SerializeEnvX`. -/
theorem hSerEnv_placed_ext_of_clone [LibsignalPlacement]
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H)
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (recordSerializeEnvSpecX Env M A lim)) :=
  recordSerializeEnv_placed_ok_ext_of_serializeX (serialize_placed_ext_of_clone hC hClone) hsub

theorem hSerEnv_placed_cl_of_clone [LibsignalPlacement]
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H)
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeEnvSpecX Env M A lim)) :=
  recordSerializeEnv_placed_cl_of_serializeX (serialize_placed_ext_of_clone hC hClone) hsub

/-- Canonical-envelope (`SerializeEnvX`) relocatable `SessionRecord::serialize` (Block `52`) from
`SerContractsXPlaced` and `SessionClonePlacedOkX`. -/
theorem hSer_placed_ext_of_clone [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (recordSerializeSpecX M A lim)) :=
  recordSerialize_placed_ok_ext_of_serializeX (serialize_placed_ext_of_clone hC hClone)

theorem hSer_placed_cl_of_clone [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeSpecX M A lim)) :=
  recordSerialize_placed_cl_of_serializeX (serialize_placed_ext_of_clone hC hClone)

theorem hSer_placed_ext_of_stage2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : Stage2ContractsPlaced A lim H)
    (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (recordSerializeSpecX M A lim)) :=
  hSer_placed_ext_of_clone (serContractsXPlaced_of_stage2ContractsPlaced hC) hClone

theorem hSer_placed_cl_of_stage2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : Stage2ContractsPlaced A lim H)
    (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeSpecX M A lim)) :=
  hSer_placed_cl_of_clone (serContractsXPlaced_of_stage2ContractsPlaced hC) hClone

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget
