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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded `SignalMessage::try_from` Slot Bridge (Placed)

Budget-pool counterparts of `tryFromSpecPlaced` and cross-block transfer for
`<SignalMessage as TryFrom<&[u8]>>::try_from` (Block `85`), parameterized by allocation envelope
`SigTryFromEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFromPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification (LibsignalPlacement lsmpl LibsignalHooks IsLsBlockProg)
open CryptoVerification.E2E.Record.Placed (lsProg_85 blkPl_85 instIsLsBlockProg_85)
open CryptoVerification.LibsignalTripleRatchetRepr (signalMessageResultAt)
open CryptoVerification.LibsignalTripleRatchet (TryFromGhost smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_rocl)

/-- Budget-threaded relocatable specification for `<SignalMessage as TryFrom<&[u8]>>::try_from` (Block `85`). -/
def tryFromSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (SigTryFromEnv : TryFromGhost → List AllocEvent → Prop) :
    Spec (TryFromGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
          FitsEnv M lim st (SigTryFromEnv x)⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ lsLogOff ∗
          stackAt s.sp smallRootStack ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ SigTryFromEnv x evs⌝ ∗
            signalMessageResultAt A.repAlloc [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
            (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗
            stackAt s0.sp smallRootStack ∗ A.pool lim (M.stepEvents evs st) sf }

/-- Hypothesis packaging the budget-threaded `SignalMessage::try_from` (Block `85`) contract. -/
structure SubsetA4SigTryFromPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (SigTryFromEnv : TryFromGhost → List AllocEvent → Prop)
    (H : LibsignalHooks) : Prop where
  sigTryFrom_placed :
    subroutine_ok (lsProg_85 H) blkPl_85.base (tryFromSpecPlaced M A lim SigTryFromEnv)

theorem cliSigTryFrom_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SigTryFromEnv : TryFromGhost → List AllocEvent → Prop} {H : LibsignalHooks}
    (hW : SubsetA4SigTryFromPlaced M A lim SigTryFromEnv H) :
    subroutine_ok (lsProg_85 H) blkPl_85.base (tryFromSpecPlaced M A lim SigTryFromEnv) := by
  exact hW.sigTryFrom_placed

/-- Transfers budget-threaded `tryFromSpecPlaced` from Block `85` to any caller block `i < 619`. -/
theorem cliSigTryFrom_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SigTryFromEnv : TryFromGhost → List AllocEvent → Prop} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hW : SubsetA4SigTryFromPlaced M A lim SigTryFromEnv H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg blkPl_85.base (tryFromSpecPlaced M A lim SigTryFromEnv) := by
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl
    (@ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_85 H) i 85 H
      hcaller (instIsLsBlockProg_85 H) blkPl_85.base _
      hW.sigTryFrom_placed _ _ _ _ hi (by decide) (by decide))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFromPlacedBudget
