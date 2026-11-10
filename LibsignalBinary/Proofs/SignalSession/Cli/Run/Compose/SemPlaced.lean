/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` Composition Semantics and Slot Specifications

Defines placed store vtable addresses (`sessVtPlaced`, `idVtPlaced`, `oneTimeVtPlaced`,
`signedVtPlaced`, `kyberVtPlaced`), `slotFramePlaced`, the placed wrapper slot contracts
(`encSlotSpecPlaced`, `decSigSlotSpecPlaced`, `initSlotSpecPlaced`, `decPkSlotSpecPlaced`), and
`slotsOfPlaced` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.RecordCodecs

/-! ## 1. Placed Store Vtable Addresses -/

def sessVtPlaced [LibsignalPlacement] : BitVec 64 := lsρ cliSessionVtSym
def idVtPlaced [LibsignalPlacement] : BitVec 64 := lsρ cliIdentityVtSym
def oneTimeVtPlaced [LibsignalPlacement] : BitVec 64 := lsρ cliPreKeyVtSym
def signedVtPlaced [LibsignalPlacement] : BitVec 64 := lsρ cliSignedPreKeyVtSym
def kyberVtPlaced [LibsignalPlacement] : BitVec 64 := lsρ cliKyberPreKeyVtSym

/-! ## 2. Placed Wrapper Slot Specs (`slotFramePlaced` & `decPkSlotSpecPlaced` from `DecryptPrekeySlotPlaced`) -/

def encSlotSpecPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) : Spec EncGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.peerA ∧ s.readReg64 .x3 = x.meA ∧
          s.readReg64 .x4 = x.stores + 0xf0#64 ∧ s.readReg64 .x5 = sessVtPlaced ∧
          s.readReg64 .x6 = x.stores ∧ s.readReg64 .x7 = idVtPlaced ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
          S.encOk x.F x.peer.val x.coins ∧ stk ≤ s.sp.toNat ∧ x.meA ≠ 0#64⌝ ∗
        slotFramePlaced A x.toSlotCtx ∗ (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s.sp unixEpoch ∗
        memRegion x.ret 248 ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) CiphertextMessage,
          ⌜slotTrace s0 sf ∧
            slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf ∧
            (∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
              m.serialized.length < 2 ^ 42)⌝ ∗
          storesAt A x.stores g' ∗ encResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun x s0 sf =>
        ⌜S.encrypt x.F x.peer.val x.me.val x.ptext x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
          anyHeap }

abbrev withCodeOk {α : Type} (CodeOk : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜CodeOk s0.mem⌝ }

def decSigSlotSpecPlacedOf [LibsignalPlacement] (CodeOk : Memory → Prop)
    (A : RustAlloc) (S : RunSem) (stk : Nat) : Spec DecSigGhost :=
  withCodeOk CodeOk
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
          s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = sessVtPlaced ∧
          s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = idVtPlaced ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
          stk ≤ s.sp.toNat⌝ ∗
        slotFramePlaced A x.toSlotCtx ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
        memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
          ⌜slotTrace s0 sf ∧
            slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf⌝ ∗
          storesAt A x.stores g' ∗ decResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun x s0 sf =>
        ⌜S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
          anyHeap }

def decSigSlotSpecPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) :
    Spec DecSigGhost :=
  decSigSlotSpecPlacedOf (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A S stk

abbrev decSigSlotSpecFrozenPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) :
    Spec DecSigGhost :=
  decSigSlotSpecPlacedOf (LibsignalFrozen lsmpl) A S stk

def initSlotSpecPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) : Spec InitGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.peerA ∧ s.readReg64 .x1 = x.meA ∧
          s.readReg64 .x2 = x.stores + 0xf0#64 ∧ s.readReg64 .x3 = sessVtPlaced ∧
          s.readReg64 .x4 = x.stores ∧ s.readReg64 .x5 = idVtPlaced ∧
          s.readReg64 .x6 = x.bundleA ∧ s.readReg64 .x7 = 0#64 ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧
          S.filesOk x.F x.peer.val x.me.val ∧ S.initOk x.F x.peer.val x.me.val ∧
          stk ≤ s.sp.toNat⌝ ∗
        slotFramePlaced A x.toSlotCtx ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) Unit,
          ⌜slotTrace s0 sf ∧
            slotOut (S.initiate x.F x.peer.val x.me.val x.bundle x.coins) g' e s0 sf⌝ ∗
          storesAt A x.stores g' ∗ initResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun x s0 sf =>
        ⌜S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
          anyHeap }

def slotsOfPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (needs : RunNeeds) : RunSlots where
  encrypt := mkSlot (encSlotSpecPlaced A S) needs.encrypt
  decryptSignal := mkSlot (decSigSlotSpecPlaced A S) needs.decryptSignal
  initiate := mkSlot (initSlotSpecPlaced A S) needs.initiate
  decryptPrekey := mkSlot (decPkSlotSpecPlaced A S) needs.decryptPrekey
  kemDeserialize := mkSlot
    (fun stk => LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (RunProofs.cliKemDeserializeSpec A stk))
    (48 + extHookStack)

def slotsOfSigFrozenPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (needs : RunNeeds) : RunSlots :=
  { slotsOfPlaced A S needs with
    decryptSignal := mkSlot (decSigSlotSpecFrozenPlaced A S) needs.decryptSignal }

def slotsOfSigPkFrozenPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (needs : RunNeeds) : RunSlots :=
  { slotsOfSigFrozenPlaced A S needs with
    decryptPrekey := mkSlot (decPkSlotSpecFrozenPlaced A S) needs.decryptPrekey }

end CryptoVerification.SignalSession.Cli.RunCompose
