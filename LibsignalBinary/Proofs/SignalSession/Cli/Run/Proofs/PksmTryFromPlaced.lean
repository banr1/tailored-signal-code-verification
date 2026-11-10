/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymE
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.ResponderWireCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `PreKeySignalMessage::try_from` Slot Bridge

Defines `pksmSlotSpecPlaced` and `pksmTryFromSpecPlaced` for
`<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`) under `[LibsignalPlacement]`, and
transfers the contract to any caller block in the session crate.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Relocatable slot specification for `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`
(Block `111`), parameterized by `S.pksmParse`. -/
def pksmSlotSpecPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) : Spec PksmGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptr ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
          CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ≤ s.sp.toNat⌝ ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ FromRecordCallees.lsLogOff ∗
        stackAt s.sp CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ pksmResAt A x.ret (S.pksmParse x.bytes) ∗ (x.ptr ↦ₛ x.bytes) ∗
          FromRecordCallees.lsLogOff ∗
          stackAt s0.sp CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

end CryptoVerification.SignalSession.Cli.RunCompose

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.RunCompose

/-- Relocatable specification for `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`)
instantiated at `Pksm.pksmParse`. -/
def pksmTryFromSpecPlaced [LibsignalPlacement] (A : RustAlloc) : Spec PksmGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptr ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
          CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ≤ s.sp.toNat⌝ ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ FromRecordCallees.lsLogOff ∗
        stackAt s.sp CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ pksmResAt A x.ret (Pksm.pksmParse x.bytes) ∗ (x.ptr ↦ₛ x.bytes) ∗
          FromRecordCallees.lsLogOff ∗
          stackAt s0.sp CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

theorem pksmSlotSpecPlaced_eq_pksmTryFromSpecPlaced [LibsignalPlacement]
    (A : RustAlloc) (S : RunSem) (hS : ∀ b, S.pksmParse b = Pksm.pksmParse b) :
    pksmSlotSpecPlaced A S = pksmTryFromSpecPlaced A := by
  have hfun : S.pksmParse = Pksm.pksmParse := funext hS
  simp only [pksmSlotSpecPlaced, pksmTryFromSpecPlaced, hfun]

/-- Hypothesis packaging `subroutine_ok` for `PreKeySignalMessage::try_from` (Block `111`) under `[LibsignalPlacement]`. -/
structure SubsetA4PksmTryFromPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  pksmTryFrom_placed :
    subroutine_ok ((CryptoVerification.blkPC_111).rebase (CryptoVerification.blkPl_111).base H)
      (CryptoVerification.blkPl_111).base (pksmTryFromSpecPlaced A)

/-- Combined hypothesis packaging `SignalMessage::try_from` (Block `85`) and
`PreKeySignalMessage::try_from` (Block `111`) under `[LibsignalPlacement]`. -/
structure SubsetA4WireCalleesPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  sigTryFrom_placed :
    subroutine_ok (E2E.Record.Placed.lsProg_85 H) (E2E.Record.Placed.blkPl_85).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        { pre := fun (x : TryFromGhost) s =>
            ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
              x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret⌝ ∗
              (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ FromRecordCallees.lsLogOff ∗
              stackAt s.sp smallRootStack ∗ A.pool
          post := fun x s0 sf =>
            ⌜sf.trace = s0.trace⌝ ∗
              signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
              (x.bytesA ↦ₛ x.bytes) ∗ FromRecordCallees.lsLogOff ∗
              stackAt s0.sp smallRootStack ∗ A.pool
          onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap })
  pksmTryFrom_placed :
    subroutine_ok ((CryptoVerification.blkPC_111).rebase (CryptoVerification.blkPl_111).base H)
      (CryptoVerification.blkPl_111).base (pksmTryFromSpecPlaced A)

theorem cliPksmTryFrom_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {S : RunSem} (hW : SubsetA4PksmTryFromPlaced A H)
    (hS : ∀ b, S.pksmParse b = Pksm.pksmParse b) :
    subroutine_ok ((CryptoVerification.blkPC_111).rebase (CryptoVerification.blkPl_111).base H)
      (CryptoVerification.blkPl_111).base (pksmSlotSpecPlaced A S) := by
  rw [pksmSlotSpecPlaced_eq_pksmTryFromSpecPlaced A S hS]
  exact hW.pksmTryFrom_placed

/-- Transfers `pksmSlotSpecPlaced` from Block `111` to any caller block `i < 619` in the session crate. -/
theorem cliPksmTryFrom_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks} {S : RunSem}
    [hcaller : IsLsBlockProg callerProg i H]
    (hW : SubsetA4PksmTryFromPlaced A H)
    (hS : ∀ b, S.pksmParse b = Pksm.pksmParse b)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (CryptoVerification.blkPl_111).base (pksmSlotSpecPlaced A S) := by
  have h111 : IsLsBlockProg
      ((CryptoVerification.blkPC_111).rebase (CryptoVerification.blkPl_111).base H) 111 H :=
    inferInstance
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((CryptoVerification.blkPC_111).rebase (CryptoVerification.blkPl_111).base H) i 111 H
    hcaller h111 (CryptoVerification.blkPl_111).base _
    (cliPksmTryFrom_placed_ok hW hS) _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

end CryptoVerification.SignalSession.Cli.RunProofs
