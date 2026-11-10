/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymE
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.ResponderWireCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFromPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded `PreKeySignalMessage::try_from` Slot Bridge (Placed)

Budget-pool counterparts of `pksmSlotSpecPlaced` and `pksmTryFromSpecPlaced` for
`<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`), parameterized by wire-decoder
allocation envelopes.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open CryptoVerification (LibsignalPlacement lsmpl LibsignalHooks IsLsBlockProg blkPC_111 blkPl_111)
open CryptoVerification.E2E.Record.Placed (lsProg_85 blkPl_85)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyTryFromStack)
open CryptoVerification.LibsignalTripleRatchet (TryFromGhost)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_rocl)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem PksmGhost pksmResAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFromPlacedBudget
  (tryFromSpecPlaced SubsetA4SigTryFromPlaced)

/-- Budget-threaded relocatable slot specification for
`<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`). -/
def pksmSlotSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) (S : RunSem) :
    Spec (PksmGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ptr ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
          preKeyTryFromStack ≤ s.sp.toNat ∧
          FitsEnv M lim st (PksmTryFromEnv x)⌝ ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ lsLogOff ∗
        stackAt s.sp preKeyTryFromStack ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ PksmTryFromEnv x evs⌝ ∗
            pksmResAt A.repAlloc x.ret (S.pksmParse x.bytes) ∗ (x.ptr ↦ₛ x.bytes) ∗
            lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗
            A.pool lim (M.stepEvents evs st) sf }

/-- Concrete `pksmParse` instance of `pksmSlotSpecPlaced` under budget pool `A`. -/
def pksmTryFromSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) :
    Spec (PksmGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ptr ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
          preKeyTryFromStack ≤ s.sp.toNat ∧
          FitsEnv M lim st (PksmTryFromEnv x)⌝ ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ lsLogOff ∗
        stackAt s.sp preKeyTryFromStack ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ PksmTryFromEnv x evs⌝ ∗
            pksmResAt A.repAlloc x.ret (pksmParse x.bytes) ∗ (x.ptr ↦ₛ x.bytes) ∗
            lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗
            A.pool lim (M.stepEvents evs st) sf }

theorem pksmSlotSpecPlaced_eq_pksmTryFromSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop)
    (S : RunSem) (hS : ∀ b, S.pksmParse b = pksmParse b) :
    pksmSlotSpecPlaced M A lim PksmTryFromEnv S = pksmTryFromSpecPlaced M A lim PksmTryFromEnv := by
  have hfun : S.pksmParse = pksmParse := funext hS
  simp only [pksmSlotSpecPlaced, pksmTryFromSpecPlaced, hfun]

/-- Hypothesis packaging the budget-threaded `PreKeySignalMessage::try_from` (Block `111`) contract. -/
structure SubsetA4PksmTryFromPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop)
    (H : LibsignalHooks) : Prop where
  pksmTryFrom_placed :
    subroutine_ok (blkPC_111.rebase blkPl_111.base H)
      blkPl_111.base (pksmTryFromSpecPlaced M A lim PksmTryFromEnv)

/-- Combined budget-threaded hypothesis for `SignalMessage::try_from` (Block `85`) and
`PreKeySignalMessage::try_from` (Block `111`). -/
structure SubsetA4WireCalleesPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (SigTryFromEnv : TryFromGhost → List AllocEvent → Prop)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop)
    (H : LibsignalHooks) : Prop where
  sigTryFrom_placed :
    subroutine_ok (lsProg_85 H) blkPl_85.base (tryFromSpecPlaced M A lim SigTryFromEnv)
  pksmTryFrom_placed :
    subroutine_ok (blkPC_111.rebase blkPl_111.base H)
      blkPl_111.base (pksmTryFromSpecPlaced M A lim PksmTryFromEnv)

theorem SubsetA4WireCalleesPlaced.toSigTryFrom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SigTryFromEnv : TryFromGhost → List AllocEvent → Prop}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks}
    (hW : SubsetA4WireCalleesPlaced M A lim SigTryFromEnv PksmTryFromEnv H) :
    SubsetA4SigTryFromPlaced M A lim SigTryFromEnv H :=
  ⟨hW.sigTryFrom_placed⟩

theorem SubsetA4WireCalleesPlaced.toPksmTryFrom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SigTryFromEnv : TryFromGhost → List AllocEvent → Prop}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks}
    (hW : SubsetA4WireCalleesPlaced M A lim SigTryFromEnv PksmTryFromEnv H) :
    SubsetA4PksmTryFromPlaced M A lim PksmTryFromEnv H :=
  ⟨hW.pksmTryFrom_placed⟩

theorem cliPksmTryFrom_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {S : RunSem}
    (hW : SubsetA4PksmTryFromPlaced M A lim PksmTryFromEnv H)
    (hS : ∀ b, S.pksmParse b = pksmParse b) :
    subroutine_ok (blkPC_111.rebase blkPl_111.base H)
      blkPl_111.base (pksmSlotSpecPlaced M A lim PksmTryFromEnv S) := by
  rw [pksmSlotSpecPlaced_eq_pksmTryFromSpecPlaced M A lim PksmTryFromEnv S hS]
  exact hW.pksmTryFrom_placed

/-- Transfers the budget-threaded `pksmSlotSpecPlaced` contract from Block `111` to any caller block `i < 619`. -/
theorem cliPksmTryFrom_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {S : RunSem}
    [hcaller : IsLsBlockProg callerProg i H]
    (hW : SubsetA4PksmTryFromPlaced M A lim PksmTryFromEnv H)
    (hS : ∀ b, S.pksmParse b = pksmParse b)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg blkPl_111.base (pksmSlotSpecPlaced M A lim PksmTryFromEnv S) := by
  have h111 : IsLsBlockProg (blkPC_111.rebase blkPl_111.base H) 111 H := inferInstance
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl
    (@ls_subroutine_ok_rocl_of_block _ _ callerProg
      (blkPC_111.rebase blkPl_111.base H) i 111 H
      hcaller h111 blkPl_111.base _
      (cliPksmTryFrom_placed_ok hW hS) _ _ _ _ hi (by decide) (by decide))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
