/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneXBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExtBudget

/-!
# Budget-Threaded Relocatable `SessionRecord::serialize` Glue

Instantiates `HSerXBudget` with `SessionCloneXBudget.sessionClone_placed_ok_ext` so
`SerContractsXPlaced M A lim H` alone discharges `serializeSpecX`, `serializeCanonSpecX`,
`recordSerializeSpecX`, and `recordSerializeEnvSpecX` on Block `52`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.E2E.Record.Placed (lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_cl_to_lscro)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget
  (hSer_placed_cl_of_clone hSer_placed_ext_of_clone hSerEnv_placed_cl_of_clone
   hSerEnv_placed_ext_of_clone serialize_placed_cl_of_clone serialize_placed_ext_of_clone)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExtBudget
  (recordSerializeEnvSpecX recordSerializeSpecX serializeCanonX_of_serialize_placedX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneXBudget
  (sessionClone_placed_ok_ext)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
  (SerContractsXPlaced SerializeEnvX serializeCanonSpecX serializeSpecX)

/-- Relocatable `[LibsignalPlacement]` `serializeSpecX M A lim` on Block `52` from
`SerContractsXPlaced M A lim H` alone. -/
theorem serialize_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeSpecX M A lim)) :=
  serialize_placed_ext_of_clone hC (sessionClone_placed_ok_ext hC)

theorem serialize_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializeSpecX M A lim)) :=
  serialize_placed_cl_of_clone hC (sessionClone_placed_ok_ext hC)

theorem serialize_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeSpecX M A lim)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serialize_placed_ok_of_serContractsX hC) hblk

/-- Relocatable `[LibsignalPlacement]` `serializeCanonSpecX M A lim` on Block `52` from
`SerContractsXPlaced M A lim H`. -/
theorem serializeCanonX_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)) :=
  serializeCanonX_of_serialize_placedX (serialize_placed_ok_of_serContractsX hC)

theorem serializeCanonX_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializeCanonSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (serializeCanonX_placed_ok_of_serContractsX hC)

theorem serializeCanonX_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCanonSpecX M A lim)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializeCanonX_placed_ok_of_serContractsX hC) hblk

/-- Relocatable `[LibsignalPlacement]` `recordSerializeSpecX M A lim` (`SerializeEnvX`) on
Block `52` from `SerContractsXPlaced M A lim H` alone. -/
theorem hSer_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (recordSerializeSpecX M A lim)) :=
  hSer_placed_ext_of_clone hC (sessionClone_placed_ok_ext hC)

theorem hSer_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeSpecX M A lim)) :=
  hSer_placed_cl_of_clone hC (sessionClone_placed_ok_ext hC)

theorem hSer_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (recordSerializeSpecX M A lim)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (hSer_placed_ok_of_serContractsX hC) hblk

/-- Parametric-envelope relocatable `[LibsignalPlacement]` `recordSerializeEnvSpecX Env M A lim` on
Block `52` from `SerContractsXPlaced M A lim H` alone. -/
theorem hSerEnv_placed_ok_of_serContractsX [LibsignalPlacement]
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs) :
    subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (recordSerializeEnvSpecX Env M A lim)) :=
  hSerEnv_placed_ext_of_clone hC (sessionClone_placed_ok_ext hC) hsub

theorem hSerEnv_placed_cl_of_serContractsX [LibsignalPlacement]
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeEnvSpecX Env M A lim)) :=
  hSerEnv_placed_cl_of_clone hC (sessionClone_placed_ok_ext hC) hsub

theorem hSerEnv_placed_lscro_of_serContractsX [LibsignalPlacement]
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (recordSerializeEnvSpecX Env M A lim)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (hSerEnv_placed_ok_of_serContractsX hC hsub) hblk

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
