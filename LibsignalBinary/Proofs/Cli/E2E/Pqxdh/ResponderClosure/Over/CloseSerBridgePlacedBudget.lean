/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgeBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneSeqFreeXBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1PlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced

/-!
# Budget-Threaded Placed `SessionRecord::serialize` (`Prev1`) Bridge and CLI Glue

Closes the relocatable `[LibsignalPlacement]` body, canonical, and 48-byte contracts for
`<SessionRecord>::serialize` (block 52) with one previous session from `SerContractsXPlaced`, under
both `SerializePrev1EnvX` and the sequence-free `SerializePrev1Env`, and instantiates them at
`cliGhostExterns` for `CliGhostAllocHooks` and `CliAllocHooks`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.E2E.Record.Placed (blkPl_52 lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_cl_to_lscro)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget
  (serializePrev1SpecWithEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlacedBudget
  (SerializePrev1PlacedOkWithEnvStmt)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyAPlacedBudget
  (serField2_placed_step)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyPlacedBudget
  (SerializePrev1AllocEnvX SerializePrev1EnvX serializePrev1Body_placed_ok)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgeBudget
  (SerPrev1CalleeContractsPlaced serPrev1Callees_placed_of_serContractsX
   serPrev1Callees_placed_of_stage2 serializePrev1CanonSpecWithEnvX serializePrev1CanonSpecX
   serializePrev1CanonX_of_body_placed serializePrev1CanonX_of_body_placed_withEnv
   serializePrev1CanonX_placed_cl_of_body_withEnv serializePrev1_placed_bridge
   serializePrev1_placed_bridge_withEnv serializePrev1_placed_cl_of_body_withEnv
   serializePrev1_placed_ok_codeLoaded serializePrev1_placed_ok_codeLoaded_withEnv
   serializePrev1_placed_ok_of_serContractsX_with
   serializePrev1Body_placed_ok_of_serContractsX_with)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget
  (SerializePrev1BodyPlacedOkWithEnvStmt serializePrev1BodyPlacedOkWithEnvStmt_mono
   serializePrev1BodySpecWithEnvX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget (CliAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks bumpGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
  (SlotsCliAllocHooks SlotsCliGhostAllocHooks cliAllocHooks_to_bumpGhost
   cliAllocHooks_to_slots serContractsX_cli_placed)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyPlacedBudget
  (SerializePrev1AllocEnvX SerializePrev1EnvX)
export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgeBudget
  (SerPrev1CalleeContractsPlaced serPrev1Callees_placed_of_serContractsX
   serPrev1Callees_placed_of_stage2 serializePrev1CanonSpecWithEnvX serializePrev1CanonSpecX
   serializePrev1CanonX_of_body_placed serializePrev1CanonX_of_body_placed_withEnv
   serializePrev1_placed_bridge serializePrev1_placed_bridge_withEnv
   serializePrev1_placed_ok_codeLoaded serializePrev1_placed_ok_codeLoaded_withEnv)

/-- Definitional equality between `StoreSessionPrev1PlacedBudget.serializePrev1BodySpecX` and
`CloseSerDefsPlacedBudget.serializePrev1BodySpecWithEnvX`. -/
theorem storeSerializePrev1BodySpecX_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop) :
    LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1PlacedBudget.serializePrev1BodySpecX
        A lim Env =
      serializePrev1BodySpecWithEnvX M A lim Env :=
  rfl

/-! ## Closed Placed Contracts from `SerContractsXPlaced` -/

/-- Closes `SerializePrev1BodyPlacedOkWithEnvStmt` at `SerializePrev1EnvX` from
`SerContractsXPlaced`. -/
theorem serializePrev1Body_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    SerializePrev1BodyPlacedOkWithEnvStmt M A lim H SerializePrev1EnvX :=
  serializePrev1Body_placed_ok_of_serContractsX_with hC
    (serField2_placed_step hC)
    (serializePrev1Body_placed_ok hC)

theorem serializePrev1BodyEnv_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env :=
  serializePrev1BodyPlacedOkWithEnvStmt_mono hsub
    (serializePrev1Body_placed_ok_of_serContractsX hC)

theorem serializePrev1_placed_codeLoaded_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1SpecWithEnv M A lim SerializePrev1EnvX)) :=
  serializePrev1_placed_ok_codeLoaded_withEnv
    (serializePrev1Body_placed_ok_of_serContractsX hC)
    (fun _ _ _ _ hev => hev)

theorem serializePrev1Env_placed_codeLoaded_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1SpecWithEnv M A lim Env)) :=
  serializePrev1_placed_ok_codeLoaded_withEnv
    (serializePrev1Body_placed_ok_of_serContractsX hC) hsub

theorem serializePrev1_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    SerializePrev1PlacedOkWithEnvStmt (lsProg_52 H) M A lim SerializePrev1EnvX :=
  serializePrev1_placed_ok_of_serContractsX_with hC
    (serField2_placed_step hC)
    (serializePrev1Body_placed_ok hC)

theorem serializePrev1Env_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    SerializePrev1PlacedOkWithEnvStmt (lsProg_52 H) M A lim Env :=
  serializePrev1_placed_cl_of_body_withEnv
    (serializePrev1Body_placed_ok_of_serContractsX hC) hsub

theorem serializePrev1CanonX_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1CanonX_of_body_placed_withEnv
    (serializePrev1Body_placed_ok_of_serContractsX hC)
    (fun _ _ _ _ hev => hev)

theorem serializePrev1CanonXEnv_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env)) :=
  serializePrev1CanonX_of_body_placed_withEnv
    (serializePrev1Body_placed_ok_of_serContractsX hC) hsub

theorem serializePrev1Body_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1EnvX)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 52)
    (serializePrev1Body_placed_ok_of_serContractsX hC)

theorem serializePrev1BodyEnv_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1BodySpecWithEnvX M A lim Env)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 52)
    (serializePrev1BodyEnv_placed_ok_of_serContractsX hC hsub)

theorem serializePrev1_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    SerializePrev1PlacedOkWithEnvStmt callerProg M A lim SerializePrev1EnvX :=
  serializePrev1_placed_cl_of_body_withEnv
    (serializePrev1Body_placed_ok_of_serContractsX hC)
    (fun _ _ _ _ hev => hev)

theorem serializePrev1Env_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    SerializePrev1PlacedOkWithEnvStmt callerProg M A lim Env :=
  serializePrev1_placed_cl_of_body_withEnv
    (serializePrev1Body_placed_ok_of_serContractsX hC) hsub

theorem serializePrev1CanonX_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1CanonX_placed_cl_of_body_withEnv
    (serializePrev1Body_placed_ok_of_serContractsX hC)
    (fun _ _ _ _ hev => hev)

theorem serializePrev1CanonXEnv_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env)) :=
  serializePrev1CanonX_placed_cl_of_body_withEnv
    (serializePrev1Body_placed_ok_of_serContractsX hC) hsub

theorem serializePrev1Body_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1EnvX)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1Body_placed_ok_of_serContractsX hC) hblk

theorem serializePrev1BodyEnv_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim Env)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1BodyEnv_placed_ok_of_serContractsX hC hsub) hblk

theorem serializePrev1CanonX_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim SerializePrev1EnvX)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1CanonX_placed_ok_of_serContractsX hC) hblk

theorem serializePrev1CanonXEnv_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1CanonXEnv_placed_ok_of_serContractsX hC hsub) hblk

theorem serializePrev1_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1SpecWithEnv M A lim SerializePrev1EnvX)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1_placed_codeLoaded_of_serContractsX hC) hblk

theorem serializePrev1Env_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1SpecWithEnv M A lim Env)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1Env_placed_codeLoaded_of_serContractsX hC hsub) hblk

/-! ## CLI Contracts under `CliGhostAllocHooks` -/

/-- Instantiates `serializePrev1BodySpecWithEnvX` (`SerializePrev1EnvX`) on block 52 at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem serializePrev1Body_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1Body_placed_ok_of_serContractsX (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1Body_cli_placed_cl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1Body_placed_cl_of_serContractsX (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1Body_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1Body_placed_lscro_of_serContractsX (serContractsX_cli_placed mmpl gh W hG) hblk

theorem serializePrev1BodyEnv_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim Env)) :=
  serializePrev1BodyEnv_placed_ok_of_serContractsX (serContractsX_cli_placed mmpl gh W hG) hsub

theorem serializePrev1BodyEnv_cli_placed_cl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1BodySpecWithEnvX M A lim Env)) :=
  serializePrev1BodyEnv_placed_cl_of_serContractsX (serContractsX_cli_placed mmpl gh W hG) hsub

theorem serializePrev1BodyEnv_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim Env)) :=
  serializePrev1BodyEnv_placed_lscro_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG) hsub hblk

theorem serializePrev1CanonX_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1CanonX_placed_ok_of_serContractsX (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1CanonX_cli_placed_cl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1CanonX_placed_cl_of_serContractsX (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1CanonX_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1CanonX_placed_lscro_of_serContractsX (serContractsX_cli_placed mmpl gh W hG) hblk

theorem serializePrev1CanonXEnv_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env)) :=
  serializePrev1CanonXEnv_placed_ok_of_serContractsX (serContractsX_cli_placed mmpl gh W hG) hsub

theorem serializePrev1CanonXEnv_cli_placed_cl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env)) :=
  serializePrev1CanonXEnv_placed_cl_of_serContractsX (serContractsX_cli_placed mmpl gh W hG) hsub

theorem serializePrev1CanonXEnv_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env)) :=
  serializePrev1CanonXEnv_placed_lscro_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG) hsub hblk

theorem serializePrev1_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1SpecWithEnv M A lim SerializePrev1EnvX)) :=
  serializePrev1_placed_codeLoaded_of_serContractsX (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1_cli_placed_cl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh) :
    SerializePrev1PlacedOkWithEnvStmt callerProg M A lim SerializePrev1EnvX :=
  serializePrev1_placed_cl_of_serContractsX (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1SpecWithEnv M A lim SerializePrev1EnvX)) :=
  serializePrev1_placed_lscro_of_serContractsX (serContractsX_cli_placed mmpl gh W hG) hblk

theorem serializePrev1Env_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1SpecWithEnv M A lim Env)) :=
  serializePrev1Env_placed_codeLoaded_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG) hsub

theorem serializePrev1Env_cli_placed_cl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    SerializePrev1PlacedOkWithEnvStmt callerProg M A lim Env :=
  serializePrev1Env_placed_cl_of_serContractsX (serContractsX_cli_placed mmpl gh W hG) hsub

theorem serializePrev1Env_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1SpecWithEnv M A lim Env)) :=
  serializePrev1Env_placed_lscro_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG) hsub hblk

/-! ## CLI Contracts under `CliAllocHooks` (`bumpGhost`) -/

/-- Instantiates `serializePrev1BodySpecWithEnvX` (`SerializePrev1EnvX`) on block 52 at
`cliGhostExterns bumpGhost (cliExternsPlaced mmpl W)` from `CliAllocHooks`. -/
theorem serializePrev1Body_placed_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim) :
    subroutine_ok (lsProg_52 (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1Body_cli_placed mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

theorem serializePrev1Body_placed_cl_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1Body_cli_placed_cl mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

theorem serializePrev1Body_placed_lscro_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1Body_cli_placed_lscro mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hblk

theorem serializePrev1BodyEnv_placed_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok (lsProg_52 (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim Env)) :=
  serializePrev1BodyEnv_cli_placed mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hsub

theorem serializePrev1BodyEnv_placed_cl_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1BodySpecWithEnvX M A lim Env)) :=
  serializePrev1BodyEnv_cli_placed_cl mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hsub

theorem serializePrev1BodyEnv_placed_lscro_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim Env)) :=
  serializePrev1BodyEnv_cli_placed_lscro mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hsub hblk

theorem serializePrev1CanonX_placed_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim) :
    subroutine_ok (lsProg_52 (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1CanonX_cli_placed mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

theorem serializePrev1CanonX_placed_cl_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1CanonX_cli_placed_cl mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

theorem serializePrev1CanonX_placed_lscro_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim SerializePrev1EnvX)) :=
  serializePrev1CanonX_cli_placed_lscro mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hblk

theorem serializePrev1CanonXEnv_placed_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok (lsProg_52 (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env)) :=
  serializePrev1CanonXEnv_cli_placed mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hsub

theorem serializePrev1CanonXEnv_placed_cl_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env)) :=
  serializePrev1CanonXEnv_cli_placed_cl mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hsub

theorem serializePrev1CanonXEnv_placed_lscro_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env)) :=
  serializePrev1CanonXEnv_cli_placed_lscro mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hsub hblk

theorem serializePrev1_placed_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim) :
    subroutine_ok (lsProg_52 (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1SpecWithEnv M A lim SerializePrev1EnvX)) :=
  serializePrev1_cli_placed mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

theorem serializePrev1_placed_cl_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim) :
    SerializePrev1PlacedOkWithEnvStmt callerProg M A lim SerializePrev1EnvX :=
  serializePrev1_cli_placed_cl mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

theorem serializePrev1_placed_lscro_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1SpecWithEnv M A lim SerializePrev1EnvX)) :=
  serializePrev1_cli_placed_lscro mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hblk

theorem serializePrev1Env_placed_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    subroutine_ok (lsProg_52 (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1SpecWithEnv M A lim Env)) :=
  serializePrev1Env_cli_placed mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hsub

theorem serializePrev1Env_placed_cl_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs) :
    SerializePrev1PlacedOkWithEnvStmt callerProg M A lim Env :=
  serializePrev1Env_cli_placed_cl mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hsub

theorem serializePrev1Env_placed_lscro_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim)
    (hsub : ∀ G sess enc evs, SerializePrev1EnvX G sess enc evs → Env G sess enc evs)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1SpecWithEnv M A lim Env)) :=
  serializePrev1Env_cli_placed_lscro mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA) hsub hblk

/-! ## Sequence-Free (`SerializePrev1Env`) Contracts and CLI Glue -/

section SeqFree

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget
  (SerializePrev1Env serializePrev1Spec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlacedBudget
  (SerializePrev1PlacedOkStmt)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyPlacedBudget
  (serializePrev1Body_seqFree_placed_ok)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgeBudget
  (serializePrev1CanonX_placed_cl_of_body serializePrev1_placed_cl_of_body)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget
  (serializePrev1BodySpecX)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget
  (SerializePrev1BodyPlacedOkStmt serializePrev1BodySpecWithEnvX_eq)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneSeqFreeXBudget
  (sessionClone_seg_placed_ok_ext)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget
  (encodeRawPrealloc_placed_ok_of_serContractsX)

/-- Closes `SerializePrev1BodyPlacedOkStmt` (`SerializePrev1Env`) from `SerContractsXPlaced`. -/
theorem serializePrev1Body_seqFree_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    SerializePrev1BodyPlacedOkStmt M A lim H := by
  have hc := serPrev1Callees_placed_of_serContractsX hC
  exact serializePrev1Body_seqFree_placed_ok hC
    (sessionClone_seg_placed_ok_ext hC)
    hc.encodeVarint
    (encodeRawPrealloc_placed_ok_of_serContractsX hC)
    hc.vecVecClone1
    (serField2_placed_step hC hc.doReserve hc.encodeVarint)
    hc.tail

theorem serializePrev1Body_seqFree_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1Env)) := by
  rw [serializePrev1BodySpecWithEnvX_eq]
  exact ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 52)
    (serializePrev1Body_seqFree_placed_ok_of_serContractsX hC)

theorem serializePrev1Body_seqFree_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1Env)) := by
  rw [serializePrev1BodySpecWithEnvX_eq]
  exact ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1Body_seqFree_placed_ok_of_serContractsX hC) hblk

theorem serializePrev1_seqFree_placed_codeLoaded_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1Spec M A lim)) :=
  serializePrev1_placed_ok_codeLoaded
    (serializePrev1Body_seqFree_placed_ok_of_serContractsX hC)

theorem serializePrev1_seqFree_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    SerializePrev1PlacedOkStmt (lsProg_52 H) M A lim :=
  serializePrev1_placed_cl_of_body
    (serializePrev1Body_seqFree_placed_ok_of_serContractsX hC)

theorem serializePrev1_seqFree_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    SerializePrev1PlacedOkStmt callerProg M A lim :=
  serializePrev1_placed_cl_of_body
    (serializePrev1Body_seqFree_placed_ok_of_serContractsX hC)

theorem serializePrev1_seqFree_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1Spec M A lim)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1_seqFree_placed_codeLoaded_of_serContractsX hC) hblk

theorem serializePrev1CanonX_seqFree_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecX M A lim)) :=
  serializePrev1CanonX_of_body_placed
    (serializePrev1Body_seqFree_placed_ok_of_serContractsX hC)

theorem serializePrev1CanonX_seqFree_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecX M A lim)) :=
  serializePrev1CanonX_placed_cl_of_body
    (serializePrev1Body_seqFree_placed_ok_of_serContractsX hC)

theorem serializePrev1CanonX_seqFree_placed_lscro_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1CanonSpecX M A lim)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1CanonX_seqFree_placed_ok_of_serContractsX hC) hblk

theorem serializePrev1Body_seqFree_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1Env)) := by
  rw [serializePrev1BodySpecWithEnvX_eq]
  exact serializePrev1Body_seqFree_placed_ok_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1Body_seqFree_cli_placed_cl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1Env)) :=
  serializePrev1Body_seqFree_placed_cl_of_serContractsX (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1Body_seqFree_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim SerializePrev1Env)) :=
  serializePrev1Body_seqFree_placed_lscro_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG) hblk

theorem serializePrev1CanonX_seqFree_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecX M A lim)) :=
  serializePrev1CanonX_seqFree_placed_ok_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1CanonX_seqFree_cli_placed_cl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecX M A lim)) :=
  serializePrev1CanonX_seqFree_placed_cl_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1CanonX_seqFree_cli_placed_lscro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1CanonSpecX M A lim)) :=
  serializePrev1CanonX_seqFree_placed_lscro_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG) hblk

theorem serializePrev1_seqFree_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1Spec M A lim)) :=
  serializePrev1_seqFree_placed_codeLoaded_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1_seqFree_cli_placed_cl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh) :
    SerializePrev1PlacedOkStmt callerProg M A lim :=
  serializePrev1_seqFree_placed_cl_of_serContractsX (serContractsX_cli_placed mmpl gh W hG)

theorem serializePrev1_seqFree_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1Spec M A lim)) :=
  serializePrev1_seqFree_placed_lscro_of_serContractsX
    (serContractsX_cli_placed mmpl gh W hG) hblk

end SeqFree

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlacedBudget
