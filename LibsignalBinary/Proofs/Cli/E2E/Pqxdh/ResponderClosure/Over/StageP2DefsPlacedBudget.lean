/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlacedBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.HelpersBudget

/-!
# Budget-Threaded Placed Stage P2 Over-Path Callee Contracts

Exposes `[LibsignalPlacement]` block-518 program aliases together with `VmPreserved`
`promote_matching_session` miss contracts (block 50) and `RustCliAllocBudget M` `promote_state`
contracts (block 47) from `StageP2DefsBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2 (clearPending clearPendingGhost)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  P2PromoteMatchingMissCallGhost P2PromoteMissGhost
  P2PromoteOverCallGhost P2PromoteOverGenGhost P2SessMatchesMsg
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget (
  PromoteOverAllocMidEnv
  PromoteOverEnv
  p2PromoteMatchingMissAtSpec
  p2PromoteMatchingMissGenSpec
  p2PromoteMatchingMissAtSpecExt
  p2PromoteMatchingMissGenSpecExt
  promoteMatchingMissAt_of_gen
  promoteMatchingMissAt_of_gen_ext
  promoteMatchingMissAt_to_ext
  p2PromoteOverAtSpecWithEnv
  p2PromoteOverAtSpec
  p2PromoteOverGenSpecWithEnv
  p2PromoteOverGenSpec
  promoteOverAt_of_gen_withEnv
  promoteOverAt_of_gen
)

noncomputable abbrev stageP2OverProgPlaced [LibsignalPlacement]
    (ext : String → Option (State → State)) : Program :=
  lsProg_518 ext

noncomputable abbrev stageP2OverEntryPlaced [LibsignalPlacement] : BitVec 64 :=
  (blkPl_518).base

abbrev PromoteMatchingMissAtPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Prop :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess msgVer serBytes

abbrev PromoteMatchingMissGenPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteMatchingMissGenPlacedProp A ext

abbrev PromoteMatchingMissAtExtPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Prop :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteMatchingMissAtExtPlacedProp A ext coroPtr g recG sess msgVer serBytes

abbrev PromoteMatchingMissGenExtPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteMatchingMissGenExtPlacedProp A ext

theorem promoteMatchingMissAt_placed_of_gen [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hGen : PromoteMatchingMissGenPlacedProp A ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8))
    (hmiss : ¬ P2SessMatchesMsg sess msgVer serBytes)
    (hlen : serBytes.length = 33) :
    PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess msgVer serBytes :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.promoteMatchingMissAt_placed_of_gen hGen coroPtr g recG sess msgVer serBytes
    hmiss hlen

theorem promoteMatchingMissAt_ext_placed_of_gen [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hGen : PromoteMatchingMissGenExtPlacedProp A ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8))
    (hmiss : ¬ P2SessMatchesMsg sess msgVer serBytes)
    (hlen : serBytes.length = 33) :
    PromoteMatchingMissAtExtPlacedProp A ext coroPtr g recG sess msgVer serBytes :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.promoteMatchingMissAt_ext_placed_of_gen hGen coroPtr g recG sess msgVer serBytes
    hmiss hlen

theorem promoteMatchingMissAt_placed_to_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {coroPtr : BitVec 64} {g : RecordGhost} {recG : SessionGhost}
    {sess : Session (List (BitVec 8))} {msgVer : BitVec 8} {serBytes : List (BitVec 8)}
    (h : PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess msgVer serBytes) :
    PromoteMatchingMissAtExtPlacedProp A ext coroPtr g recG sess msgVer serBytes :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.promoteMatchingMissAt_placed_to_ext h

abbrev PromoteOverAtPlacedWithEnvProp [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Prop :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteOverAtPlacedWithEnvProp M A lim Env ext coroPtr g recG sess

abbrev PromoteOverAtPlacedProp [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Prop :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteOverAtPlacedProp M A lim ext coroPtr g recG sess

abbrev PromoteOverGenPlacedWithEnvProp [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteOverGenPlacedWithEnvProp M A lim Env ext

abbrev PromoteOverGenPlacedProp [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteOverGenPlacedProp M A lim ext

theorem promoteOverAt_placed_of_gen_withEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hGen : PromoteOverGenPlacedWithEnvProp M A lim Env ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (encSessionMem (clearPendingGhost recG) (clearPending sess)).length < 2 ^ 32) :
    PromoteOverAtPlacedWithEnvProp M A lim Env ext coroPtr g recG sess :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.promoteOverAt_placed_of_gen_withEnv hGen coroPtr g recG sess hlen

theorem promoteOverAt_placed_of_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hGen : PromoteOverGenPlacedProp M A lim ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (encSessionMem (clearPendingGhost recG) (clearPending sess)).length < 2 ^ 32) :
    PromoteOverAtPlacedProp M A lim ext coroPtr g recG sess :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.promoteOverAt_placed_of_gen hGen coroPtr g recG sess hlen

theorem promoteOverGenPlacedWithEnv_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (himp : ∀ G sess evs, Env₁ G sess evs → Env₂ G sess evs)
    (h : PromoteOverGenPlacedWithEnvProp M A lim Env₁ ext) :
    PromoteOverGenPlacedWithEnvProp M A lim Env₂ ext :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.promoteOverGenPlacedWithEnv_mono himp h

theorem promoteOverAtPlacedWithEnv_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    {coroPtr : BitVec 64} {g : RecordGhost} {recG : SessionGhost}
    {sess : Session (List (BitVec 8))}
    (himp : ∀ G sess evs, Env₁ G sess evs → Env₂ G sess evs)
    (h : PromoteOverAtPlacedWithEnvProp M A lim Env₁ ext coroPtr g recG sess) :
    PromoteOverAtPlacedWithEnvProp M A lim Env₂ ext coroPtr g recG sess :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.promoteOverAtPlacedWithEnv_mono himp h

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
