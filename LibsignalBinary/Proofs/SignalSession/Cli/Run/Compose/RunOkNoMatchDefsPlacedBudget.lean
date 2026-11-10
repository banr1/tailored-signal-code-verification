/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.S_d2c
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.RunCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import Arm64.Trusted.Spec.Hoare

/-!
# Budget-Threaded Placed D2(c) Slot Predicates

Re-exports allocator-free D2(c) observation definitions and model-agreement lemmas from
`RunOkNoMatchDefsPlaced`, and defines budget-threaded `DecPkD2cSlotOkPlaced` /
`DecPkD2cSlotOkFrozenPlaced` and `PksmSlotOkPlaced` slot predicates at
`cliGhostExterns g (cliExternsPlaced mmpl W)`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111 lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliRunBudgets)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost PksmGhost RunNeeds RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOkD2c cliDecryptPrekeyNeed decPkDefD2c)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (pksmSlotSpecPlaced)

/-- Reducible synonym for `CalleeSlot.OkPlaced` (`SkeletonPlaced.lean:68`) so
`RunOkNoMatchDefsPlacedBudget` stays decoupled from `SkeletonPlaced`. -/
abbrev slotOkPlaced (callerProg : Program) (target : BitVec 64) (σ : CalleeSlot) : Prop :=
  ∀ stk, σ.need ≤ stk → stk ≤ 2 ^ 63 →
    subroutine_ok callerProg target (σ.spec stk)

/-- Extern-parametric D2(c) `decryptPrekey` slot contract on `lsProg_579 H` at fixed `(X, W)`. -/
def DecPkD2cSlotOkPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem) (needs : RunNeeds) (sEnvs : RunSlotEnvs),
    sEnvs.decryptPrekey = DecPkEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
    slotOkPlaced (lsProg_579 H) (lsmpl.base 520) (slotsOfPlaced A lim sEnvs S needs).decryptPrekey

/-- D2(c) `decryptPrekey` slot contract at `cliGhostExterns g (cliExternsPlaced mmpl W)`,
quantified over `X : UnreachedPqxdhPrimitives`. -/
def DecPkD2cSlotOkPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives),
    DecPkD2cSlotOkPlacedAt (cliGhostExterns g (cliExternsPlaced mmpl W)) X W A lim DecPkEnv

def DecPkD2cSlotOkPlacedLinked [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives),
    DecPkD2cSlotOkPlacedAt (cliExternsPlaced mmpl W) X W A lim DecPkEnv

/-- Extern-parametric D2(c) `PreKeySignalMessage::try_from` slot contract on `lsProg_579 H`. -/
def PksmSlotOkPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) : Prop :=
  ∀ S : RunSem, S.pksmParse = pksmParse →
    subroutine_ok (lsProg_579 H) (blkPl_111).base
      (pksmSlotSpecPlaced M A lim PksmTryFromEnv S)

/-- D2(c) `PreKeySignalMessage::try_from` slot contract at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
abbrev PksmSlotOkPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) : Prop :=
  PksmSlotOkPlacedAt (cliGhostExterns g (cliExternsPlaced mmpl W)) A lim PksmTryFromEnv

abbrev PksmSlotOkPlacedLinked [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) : Prop :=
  PksmSlotOkPlacedAt (cliExternsPlaced mmpl W) A lim PksmTryFromEnv


/-- Extern-parametric `LibsignalFrozen` D2(c) `decryptPrekey` slot contract on `lsProg_579 H`
at fixed `(X, W)` (`slotsOfSigPkFrozenPlaced`). -/
def DecPkD2cSlotOkFrozenPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem) (needs : RunNeeds) (sEnvs : RunSlotEnvs),
    sEnvs.decryptPrekey = DecPkEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
    slotOkPlaced (lsProg_579 H) (lsmpl.base 520)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim sEnvs S needs).decryptPrekey

/-- `LibsignalFrozen` D2(c) `decryptPrekey` slot contract at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
def DecPkD2cSlotOkFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives),
    DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns g (cliExternsPlaced mmpl W)) X W A lim DecPkEnv

def DecPkD2cSlotOkFrozenPlacedLinked [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives),
    DecPkD2cSlotOkFrozenPlacedAt (cliExternsPlaced mmpl W) X W A lim DecPkEnv

abbrev DecPkD2cSlotOkFullPlacedAt := @DecPkD2cSlotOkFrozenPlacedAt

abbrev DecPkD2cSlotOkFullPlaced := @DecPkD2cSlotOkFrozenPlaced

abbrev DecPkD2cSlotOkFullPlacedLinked := @DecPkD2cSlotOkFrozenPlacedLinked

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
