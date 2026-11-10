/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Slot Specifications

Defines `RunSlotEnvs` and the budget-threaded (`RustCliAllocBudget M`) wrapper slot contracts
`encSlotSpecPlaced`, `decSigSlotSpecPlaced`, `initSlotSpecPlaced`, `decPkSlotSpecPlaced`, and
`slotsOfPlaced` (along with `LibsignalFrozen`-guarded variants).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSessionApi (ApiError CiphertextMessage PreKeySignalMessage)
open CryptoVerification (LibsignalFrozen LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt signalMessageAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (storesAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunSlots)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Bytes DecPkGhost DecSigGhost EncGhost InitGhost RunNeeds RunSem SlotCtx
   cliBundleAt decResAt encResAt idVtPlaced initResAt kyberVtPlaced mkSlot
   nowCellAt oneTimeVtPlaced sessVtPlaced signedVtPlaced slotOut slotTrace unixEpoch)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (cliKemDeserializeSpec)

/-- Allocation-event envelopes for the four stateful wrapper slots of `signal_session::run`. -/
structure RunSlotEnvs where
  encrypt : EncGhost → List AllocEvent → Prop
  decryptSignal : DecSigGhost → List AllocEvent → Prop
  initiate : InitGhost → List AllocEvent → Prop
  decryptPrekey : DecPkGhost → List AllocEvent → Prop

abbrev slotFramePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : SlotCtx) (s : State) :
    SepProp :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced
    A lim st x s

theorem slotFramePlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : SlotCtx) (s : State) :
    slotFramePlaced A lim st x s =
      CryptoVerification.SignalSession.Cli.RunCompose.slotFramePlaced (A.atState lim st s) x :=
  rfl

/-- Budget-threaded relocatable `[LibsignalPlacement]` `encrypt` slot contract
(`signal_session_ratchet::encrypt`) carrying `withLsCodeRoLoaded lsmpl`. -/
def encSlotSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (EncEnv : EncGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (EncGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.peerA ∧ s.readReg64 .x3 = x.meA ∧
          s.readReg64 .x4 = x.stores + 0xf0#64 ∧ s.readReg64 .x5 = sessVtPlaced ∧
          s.readReg64 .x6 = x.stores ∧ s.readReg64 .x7 = idVtPlaced ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
          S.encOk x.F x.peer.val x.coins ∧ stk ≤ s.sp.toNat ∧ x.meA ≠ 0#64 ∧
          FitsEnv M lim st (EncEnv x)⌝ ∗
        slotFramePlaced A lim st x.toSlotCtx s ∗ (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s.sp unixEpoch ∗
        memRegion x.ret 248 ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent, ∃∗ g' : StoresGhost,
          ∃∗ e : Except (ApiError AddrVal Unit) CiphertextMessage,
          ⌜EncEnv x evs ∧ slotTrace s0 sf ∧
            slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf ∧
            (∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
              m.serialized.length < 2 ^ 42)⌝ ∗
          storesAt A.repAlloc x.stores g' ∗ encResAt A.repAlloc x.ret e ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun (x, _) _ _ =>
        ⌜S.encrypt x.F x.peer.val x.me.val x.ptext x.coins = none⌝ ∗ anyHeap }

/-- Budget-threaded relocatable `[LibsignalPlacement]` `decrypt_signal` slot contract
(`signal_session_ratchet::decrypt_signal`) carrying `withLsCodeRoLoaded lsmpl`. -/
def decSigSlotSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecSigGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
          s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = sessVtPlaced ∧
          s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = idVtPlaced ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
          stk ≤ s.sp.toNat ∧ FitsEnv M lim st (DecSigEnv x)⌝ ∗
        slotFramePlaced A lim st x.toSlotCtx s ∗ signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent, ∃∗ g' : StoresGhost,
          ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
          ⌜DecSigEnv x evs ∧ slotTrace s0 sf ∧
            slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf⌝ ∗
          storesAt A.repAlloc x.stores g' ∗ decResAt A.repAlloc x.ret e ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun (x, _) _ _ =>
        ⌜S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗ anyHeap }

/-- Budget-threaded relocatable `[LibsignalPlacement]` `initiate` slot contract
(`signal_session_handshake::initiate`) carrying `withLsCodeRoLoaded lsmpl`. -/
def initSlotSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (InitGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.peerA ∧ s.readReg64 .x1 = x.meA ∧
          s.readReg64 .x2 = x.stores + 0xf0#64 ∧ s.readReg64 .x3 = sessVtPlaced ∧
          s.readReg64 .x4 = x.stores ∧ s.readReg64 .x5 = idVtPlaced ∧
          s.readReg64 .x6 = x.bundleA ∧ s.readReg64 .x7 = 0#64 ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧
          S.filesOk x.F x.peer.val x.me.val ∧ S.initOk x.F x.peer.val x.me.val ∧
          stk ≤ s.sp.toNat ∧ FitsEnv M lim st (InitEnv x)⌝ ∗
        slotFramePlaced A lim st x.toSlotCtx s ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent, ∃∗ g' : StoresGhost,
          ∃∗ e : Except (ApiError AddrVal Unit) Unit,
          ⌜InitEnv x evs ∧ slotTrace s0 sf ∧
            slotOut (S.initiate x.F x.peer.val x.me.val x.bundle x.coins) g' e s0 sf⌝ ∗
          storesAt A.repAlloc x.stores g' ∗ initResAt A.repAlloc x.ret e ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun (x, _) _ _ =>
        ⌜S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none⌝ ∗ anyHeap }

abbrev decPkSlotSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced
    A lim DecPkEnv S stk

/-- Budget-threaded relocatable `[LibsignalPlacement]` wrapper slots of `signal_session::run`. -/
def slotsOfPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : RunSlotEnvs)
    (S : RunSem) (needs : RunNeeds) : RunSlots where
  encrypt := mkSlot (encSlotSpecPlaced A lim envs.encrypt S) needs.encrypt
  decryptSignal := mkSlot (decSigSlotSpecPlaced A lim envs.decryptSignal S) needs.decryptSignal
  initiate := mkSlot (initSlotSpecPlaced A lim envs.initiate S) needs.initiate
  decryptPrekey := mkSlot (decPkSlotSpecPlaced A lim envs.decryptPrekey S) needs.decryptPrekey
  kemDeserialize := mkSlot
    (fun stk => withLsCodeRoLoaded lsmpl (cliKemDeserializeSpec M A lim stk))
    (48 + extHookStack)

/-- Base (unwrapped) budget-threaded `[LibsignalPlacement]` `decrypt_signal` slot contract,
`rfl`-equal to `DecryptLemmas.TopPlacedBudget.decSigSlotSpecBasePlaced`. -/
def decSigSlotSpecBasePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecSigGhost × M.σ) :=
  { pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
        s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = sessVtPlaced ∧
        s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = idVtPlaced ∧
        s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
        stk ≤ s.sp.toNat ∧ FitsEnv M lim st (DecSigEnv x)⌝ ∗
      slotFramePlaced A lim st x.toSlotCtx s ∗ signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      memRegion x.ret 48 ∗ stackAt s.sp stk
    post := fun (x, st) s0 sf =>
      ∃∗ evs : List AllocEvent, ∃∗ g' : StoresGhost,
        ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
        ⌜DecSigEnv x evs ∧ slotTrace s0 sf ∧
          slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf⌝ ∗
        storesAt A.repAlloc x.stores g' ∗ decResAt A.repAlloc x.ret e ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        protocolAddressAt A.repAlloc x.me x.meA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ lsLogOff ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp stk ∗ anyHeap
    onPanic := fun (x, _) _ _ =>
      ⌜S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗ anyHeap }

/-- `CodeOk`-parameterized budget-threaded `[LibsignalPlacement]` `decrypt_signal` slot contract,
`rfl`-equal to `DecryptLemmas.TopPlacedBudget.decSigSlotSpecPlacedOf`. -/
def decSigSlotSpecPlacedOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecSigGhost × M.σ) :=
  CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk CodeOk
    (decSigSlotSpecBasePlaced A lim DecSigEnv S stk)

/-- `LibsignalFrozen`-guarded budget-threaded `[LibsignalPlacement]` `decrypt_signal` slot
contract (`withLsFrozen lsmpl`). -/
abbrev decSigSlotSpecFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecSigGhost × M.σ) :=
  decSigSlotSpecPlacedOf (LibsignalFrozen lsmpl) A lim DecSigEnv S stk

abbrev decPkSlotSpecFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecFrozenPlaced
    A lim DecPkEnv S stk

/-- Wrapper slots with `decryptPrekey` guarded by `LibsignalFrozen lsmpl`. -/
def slotsOfPkFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : RunSlotEnvs)
    (S : RunSem) (needs : RunNeeds) : RunSlots :=
  { slotsOfPlaced A lim envs S needs with
    decryptPrekey := mkSlot (decPkSlotSpecFrozenPlaced A lim envs.decryptPrekey S)
      needs.decryptPrekey }

/-- Wrapper slots with `decryptSignal` guarded by `LibsignalFrozen lsmpl`. -/
def slotsOfSigFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : RunSlotEnvs)
    (S : RunSem) (needs : RunNeeds) : RunSlots :=
  { slotsOfPlaced A lim envs S needs with
    decryptSignal := mkSlot (decSigSlotSpecFrozenPlaced A lim envs.decryptSignal S)
      needs.decryptSignal }

/-- Wrapper slots with both `decryptSignal` and `decryptPrekey` guarded by `LibsignalFrozen lsmpl`. -/
def slotsOfSigPkFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : RunSlotEnvs)
    (S : RunSem) (needs : RunNeeds) : RunSlots :=
  { slotsOfSigFrozenPlaced A lim envs S needs with
    decryptPrekey := mkSlot (decPkSlotSpecFrozenPlaced A lim envs.decryptPrekey S)
      needs.decryptPrekey }

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
