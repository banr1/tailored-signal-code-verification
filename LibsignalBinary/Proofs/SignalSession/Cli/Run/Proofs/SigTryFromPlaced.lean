/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymE
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `SignalMessage::try_from` Slot Bridge

Defines `tryFromSpecPlaced` for `<SignalMessage as TryFrom<&[u8]>>::try_from` (Block `85`) under
`[LibsignalPlacement]`, and transfers the contract to any caller block `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Relocatable `[LibsignalPlacement]` specification for `<SignalMessage as TryFrom<&[u8]>>::try_from` (Block `85`). -/
def tryFromSpecPlaced [LibsignalPlacement] (A : RustAlloc) : Spec TryFromGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ FromRecordCallees.lsLogOff ∗
          stackAt s.sp smallRootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ FromRecordCallees.lsLogOff ∗
          stackAt s0.sp smallRootStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

/-- Hypothesis packaging `subroutine_ok` for `SignalMessage::try_from` (Block `85`) under `[LibsignalPlacement]`. -/
structure SubsetA4SigTryFromPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  sigTryFrom_placed :
    subroutine_ok (E2E.Record.Placed.lsProg_85 H) (E2E.Record.Placed.blkPl_85).base (tryFromSpecPlaced A)

theorem cliSigTryFrom_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hW : SubsetA4SigTryFromPlaced A H) :
    subroutine_ok (E2E.Record.Placed.lsProg_85 H) (E2E.Record.Placed.blkPl_85).base (tryFromSpecPlaced A) :=
  hW.sigTryFrom_placed

/-- Transfers `tryFromSpecPlaced` from Block `85` to any caller block `i < 619`. -/
theorem cliSigTryFrom_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hW : SubsetA4SigTryFromPlaced A H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (E2E.Record.Placed.blkPl_85).base (tryFromSpecPlaced A) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (E2E.Record.Placed.lsProg_85 H) i 85 H
    hcaller (instIsLsBlockProg_85 H) (E2E.Record.Placed.blkPl_85).base _
    hW.sigTryFrom_placed _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

end CryptoVerification.SignalSession.Cli.RunProofs
