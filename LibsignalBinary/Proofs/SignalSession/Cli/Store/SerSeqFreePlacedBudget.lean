/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChainSpareXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRawSpareXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
import Arm64.Trusted.Spec.Hoare

/-!
# `RecordSerializeSeqFreeEnv` Relocatable `SessionRecord::serialize` Glue

Composes `EncodeChainSpareXBudget` (Block `12`), `EncodeRawSpareXBudget` (Block `14`), and
`SerializeSeqFreeXBudget` (Blocks `80` and `52`) so `SerContractsXPlaced M A lim H` discharges
`EncodeRawPreallocPlacedOkX` and `serialize{,Canon}SeqFreeSpecX`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.E2E.Record.Placed (lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_cl_to_lscro)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
  (EncodeRawPreallocPlacedOkX encodeRawPreallocSpecX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChainSpareXBudget
  (encodeChainPrealloc_placed_ok_of_serContractsX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRawSpareXBudget
  (encodeRawPrealloc_placed_ok_of_chain)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget
  (serializeCanonSeqFree_placed_ok_of_raw serialize_seqFree_placed_ok_of_raw)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)

abbrev serializeSeqFreeSpecX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget.serializeSeqFreeSpecX

abbrev serializeCanonSeqFreeSpecX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget.serializeCanonSeqFreeSpecX

/-- Relocatable `[LibsignalPlacement]` pre-reserved `0`-allocation Block-`14` contract
`EncodeRawPreallocPlacedOkX A.repAlloc H` from `SerContractsXPlaced M A lim H` alone. -/
theorem encodeRawPrealloc_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    EncodeRawPreallocPlacedOkX A.repAlloc H :=
  encodeRawPrealloc_placed_ok_of_chain hC (encodeChainPrealloc_placed_ok_of_serContractsX hC)

theorem encodeRawPrealloc_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 14)
      (withLsCl lsmpl (encodeRawPreallocSpecX A.repAlloc)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeRawPrealloc_placed_ok_of_serContractsX hC)

/-- Relocatable `[LibsignalPlacement]` `serializeSeqFreeSpecX M A lim` on Block `52` from
`SerContractsXPlaced M A lim H` alone. -/
theorem serialize_seqFree_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeSeqFreeSpecX M A lim)) :=
  serialize_seqFree_placed_ok_of_raw hC (encodeRawPrealloc_placed_ok_of_serContractsX hC)

theorem serialize_seqFree_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializeSeqFreeSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (serialize_seqFree_placed_ok_of_serContractsX hC)

theorem serialize_seqFree_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeSeqFreeSpecX M A lim)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serialize_seqFree_placed_ok_of_serContractsX hC) hblk

/-- Relocatable `[LibsignalPlacement]` `serializeCanonSeqFreeSpecX M A lim` on Block `52` from
`SerContractsXPlaced M A lim H` alone. -/
theorem serializeCanonSeqFree_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)) :=
  serializeCanonSeqFree_placed_ok_of_raw hC (encodeRawPrealloc_placed_ok_of_serContractsX hC)

theorem serializeCanonSeqFree_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializeCanonSeqFreeSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (serializeCanonSeqFree_placed_ok_of_serContractsX hC)

theorem serializeCanonSeqFree_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializeCanonSeqFree_placed_ok_of_serContractsX hC) hblk

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget
