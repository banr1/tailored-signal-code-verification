/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs

/-!
# Budget-Threaded `SignalMessage` MAC Specifications

`RustCliAllocBudget` contracts and exact allocator event envelopes for
`SignalMessage::serialize_addresses`, `SignalMessage::compute_mac`, and
`SignalMessage::verify_mac_with_addresses`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (IdentityKey ShaCompress SignalMessage computeMac)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (allocHookStack vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SignalMessageGhost UuidParser okTagVec protocolAddressAt
   serializeAddresses serviceIdParse signalMessageAt)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack parseSidStack
   serializeAddressesName computeMacName verifyMacWithAddressesName
   serializeAddressesStack computeMacStack verifyMacWithAddressesStack
   serializeAddressesStackX computeMacStackX verifyMacWithAddressesStackX
   optSerializeAddressesAt SerializeAddressesGhost ComputeMacGhost
   verifyMacResultAt VerifyMacWithAddressesGhost
   lsMacRustAllocSym lsMacRustDeallocSym lsMacRustNoAllocShimSym lsMacHandleErrorSym
   lsMacMemcpySym lsMacMemsetSym lsMacCompress256Sym
   mac_ls_externAt?_of_mem mac_ls_hook_ok_of_mem sepWPp_seq_lscl macLsLogOff)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (publicKeySerializeEvents publicKeySerializeStack publicKeySerializeStackX)

/-! ## Re-Exports from `Mac.Defs` -/

abbrev serializeAddressesName := CryptoVerification.LibsignalTripleRatchet.serializeAddressesName
abbrev computeMacName := CryptoVerification.LibsignalTripleRatchet.computeMacName
abbrev verifyMacWithAddressesName :=
  CryptoVerification.LibsignalTripleRatchet.verifyMacWithAddressesName
abbrev serializeAddressesStack := CryptoVerification.LibsignalTripleRatchet.serializeAddressesStack
abbrev computeMacStack := CryptoVerification.LibsignalTripleRatchet.computeMacStack
abbrev verifyMacWithAddressesStack :=
  CryptoVerification.LibsignalTripleRatchet.verifyMacWithAddressesStack
abbrev serializeAddressesStackX :=
  CryptoVerification.LibsignalTripleRatchet.serializeAddressesStackX
abbrev computeMacStackX := CryptoVerification.LibsignalTripleRatchet.computeMacStackX
abbrev verifyMacWithAddressesStackX :=
  CryptoVerification.LibsignalTripleRatchet.verifyMacWithAddressesStackX
abbrev optSerializeAddressesAt := CryptoVerification.LibsignalTripleRatchet.optSerializeAddressesAt
abbrev SerializeAddressesGhost := CryptoVerification.LibsignalTripleRatchet.SerializeAddressesGhost
abbrev ComputeMacGhost := CryptoVerification.LibsignalTripleRatchet.ComputeMacGhost
abbrev verifyMacResultAt := CryptoVerification.LibsignalTripleRatchet.verifyMacResultAt
abbrev VerifyMacWithAddressesGhost :=
  CryptoVerification.LibsignalTripleRatchet.VerifyMacWithAddressesGhost
abbrev macLsLogOff := @CryptoVerification.LibsignalTripleRatchet.macLsLogOff

/-! ## Allocator Event Lists & Envelopes -/

/-- Exact allocator event sequence of `<SignalMessage>::serialize_addresses`:
`[]` when either address fails `serviceIdParse`, and `rustAllocEvents 36 1` when both parse. -/
def serializeAddressesEvents (parse : UuidParser) (x : SerializeAddressesGhost) :
    List AllocEvent :=
  match serializeAddresses (serviceIdParse parse) x.sender x.recipient with
  | none => []
  | some _ => rustAllocEvents 36 1

def SerializeAddressesEnv (parse : UuidParser) (x : SerializeAddressesGhost)
    (evs : List AllocEvent) : Prop :=
  evs = serializeAddressesEvents parse x

theorem fitsEnv_serializeAddresses_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (parse : UuidParser) (x : SerializeAddressesGhost) :
    FitsEnv M lim st (SerializeAddressesEnv parse x) ↔
      FitsEvents M lim st (serializeAddressesEvents parse x) :=
  FitsEnv.eq_iff

/-- Exact allocator event sequence of `<SignalMessage>::compute_mac`:
two `PublicKey::serialize` allocations (`33` bytes, align `1`) each paired with
`__rust_dealloc(ptr, 33, 1)`. -/
def computeMacEvents : List AllocEvent :=
  (publicKeySerializeEvents ++ rustDeallocEvents 33 1) ++
    (publicKeySerializeEvents ++ rustDeallocEvents 33 1)

def ComputeMacEnv (evs : List AllocEvent) : Prop :=
  evs = computeMacEvents

theorem fitsEnv_computeMac_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st ComputeMacEnv ↔ FitsEvents M lim st computeMacEvents :=
  FitsEnv.eq_iff

/-- Exact allocator event sequence of `<SignalMessage>::verify_mac_with_addresses`:
`computeMacEvents`, followed (when the 8-byte MAC matches, `x.msg.addresses.isSome`, and
`serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr` is `some _`) by
`rustAllocEvents 36 1 ++ rustDeallocEvents 36 1`. -/
def verifyMacWithAddressesEvents (F : ShaCompress) (parse : UuidParser)
    (x : VerifyMacWithAddressesGhost) : List AllocEvent :=
  let macMatches :=
    computeMac F x.senderIk x.receiverIk x.macKey
      (x.msg.serialized.take (x.msg.serialized.length - 8)) ==
      x.msg.serialized.drop (x.msg.serialized.length - 8)
  if macMatches && x.msg.addresses.isSome &&
      (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr).isSome then
    computeMacEvents ++ (rustAllocEvents 36 1 ++ rustDeallocEvents 36 1)
  else
    computeMacEvents

def VerifyMacWithAddressesEnv (F : ShaCompress) (parse : UuidParser)
    (x : VerifyMacWithAddressesGhost) (evs : List AllocEvent) : Prop :=
  evs = verifyMacWithAddressesEvents F parse x

theorem fitsEnv_verifyMacWithAddresses_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (F : ShaCompress) (parse : UuidParser) (x : VerifyMacWithAddressesGhost) :
    FitsEnv M lim st (VerifyMacWithAddressesEnv F parse x) ↔
      FitsEvents M lim st (verifyMacWithAddressesEvents F parse x) :=
  FitsEnv.eq_iff

/-! ## `SignalMessage::serialize_addresses` budget contracts -/

/-- Stack-parameterized budget contract of `<SignalMessage>::serialize_addresses`
(`saStack = serializeAddressesStack` or `serializeAddressesStackX`).
Under `FitsEnv M lim st (SerializeAddressesEnv parse x)`, `onPanic = ⌜False⌝` and
`onOom = ⌜False⌝`. -/
def serializeAddressesSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (parse : UuidParser) (saStack : Nat) :
    Spec (SerializeAddressesGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.senderA ∧ s.readReg64 .x2 = x.recipientA ∧
      FitsEnv M lim st (SerializeAddressesEnv parse x)⌝ ∗
      protocolAddressAt A.repAlloc x.sender x.senderA ∗
      protocolAddressAt A.repAlloc x.recipient x.recipientA ∗
      memRegion x.ret 24 ∗ A.pool lim st s ∗ stackAt s.sp saStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protocolAddressAt A.repAlloc x.sender x.senderA ∗
      protocolAddressAt A.repAlloc x.recipient x.recipientA ∗
      optSerializeAddressesAt A.repAlloc x.ret
        (serializeAddresses (serviceIdParse parse) x.sender x.recipient) ∗
      A.pool lim (M.stepEvents (serializeAddressesEvents parse x) st) sf ∗
      stackAt s0.sp saStack

/-- `serializeAddressesSpecWithStack` parameterized by callee stack `callStack`
(total stack `callStack + 128`). -/
abbrev serializeAddressesSpecAt (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (parse : UuidParser) (callStack : Nat) :
    Spec (SerializeAddressesGhost × M.σ) :=
  serializeAddressesSpecWithStack M A lim parse (callStack + 128)

abbrev serializeAddressesSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (parse : UuidParser) :
    Spec (SerializeAddressesGhost × M.σ) :=
  serializeAddressesSpecWithStack M A lim parse serializeAddressesStack

abbrev serializeAddressesSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (parse : UuidParser) :
    Spec (SerializeAddressesGhost × M.σ) :=
  serializeAddressesSpecWithStack M A lim parse serializeAddressesStackX

abbrev serializeAddressesBudgetSpecWithStack := @serializeAddressesSpecWithStack
abbrev serializeAddressesBudgetSpecAt := @serializeAddressesSpecAt
abbrev serializeAddressesBudgetSpec := @serializeAddressesSpec
abbrev serializeAddressesBudgetSpecX := @serializeAddressesSpecX

/-! ## `SignalMessage::compute_mac` budget contracts -/

/-- Stack-parameterized budget contract of `<SignalMessage>::compute_mac`
(`cmStack = computeMacStack` or `computeMacStackX`).
Under `FitsEnv M lim st ComputeMacEnv`, `onPanic = ⌜False⌝` and `onOom = ⌜False⌝`. -/
def computeMacSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (cmStack : Nat) :
    Spec (ComputeMacGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.senderA ∧ s.readReg64 .x2 = x.receiverA ∧
      s.readReg64 .x3 = x.keyA ∧ s.readReg64 .x4 = 32#64 ∧ s.readReg64 .x5 = x.msgA ∧
      (s.readReg64 .x6).toNat = x.message.length ∧ x.message.length < 2 ^ 63 ∧
      FitsEnv M lim st ComputeMacEnv⌝ ∗
      memRegion x.ret 16 ∗
      (x.senderA ↦ₛ x.sender.publicKey.bytes.toList) ∗
      (x.receiverA ↦ₛ x.receiver.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      (x.msgA ↦ₛ x.message) ∗
      A.pool lim st s ∗ stackAt s.sp cmStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦₆₄ okTagVec) ∗
      ((x.ret + 8#64) ↦ₛ computeMac F x.sender x.receiver x.macKey x.message) ∗
      (x.senderA ↦ₛ x.sender.publicKey.bytes.toList) ∗
      (x.receiverA ↦ₛ x.receiver.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      (x.msgA ↦ₛ x.message) ∗
      A.pool lim (M.stepEvents computeMacEvents st) sf ∗ stackAt s0.sp cmStack

/-- `computeMacSpecWithStack` parameterized by `PublicKey::serialize` stack `pkStack`
(total stack `pkStack + 496`). -/
abbrev computeMacSpecAt (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (pkStack : Nat) :
    Spec (ComputeMacGhost × M.σ) :=
  computeMacSpecWithStack M A lim F (pkStack + 496)

abbrev computeMacSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (ComputeMacGhost × M.σ) :=
  computeMacSpecWithStack M A lim F computeMacStack

abbrev computeMacSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (ComputeMacGhost × M.σ) :=
  computeMacSpecWithStack M A lim F computeMacStackX

abbrev computeMacBudgetSpecWithStack := @computeMacSpecWithStack
abbrev computeMacBudgetSpecAt := @computeMacSpecAt
abbrev computeMacBudgetSpec := @computeMacSpec
abbrev computeMacBudgetSpecX := @computeMacSpecX

/-! ## `SignalMessage::verify_mac_with_addresses` placed budget contracts -/

/-- Stack-parameterized relocatable `[LibsignalPlacement]` budget contract of
`<SignalMessage>::verify_mac_with_addresses` (Block `62`).
Under `FitsEnv M lim st (VerifyMacWithAddressesEnv F parse x)`, `onPanic = ⌜False⌝` and
`onOom = ⌜False⌝`. -/
def verifyMacWithAddressesPlacedSpecWithStack [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) (parse : UuidParser)
    (totalStack : Nat) : Spec (VerifyMacWithAddressesGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.senderAddrA ∧
      s.readReg64 .x2 = x.receiverAddrA ∧ s.readReg64 .x3 = x.senderIkA ∧
      s.readReg64 .x4 = x.receiverIkA ∧ s.readReg64 .x5 = x.keyA ∧
      s.readReg64 .x6 = 32#64 ∧ s.readReg64 .x8 = x.ret ∧
      FitsEnv M lim st (VerifyMacWithAddressesEnv F parse x)⌝ ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
      protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
      (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      memRegion x.ret 9 ∗
      macLsLogOff ∗
      A.pool lim st s ∗ stackAt s.sp totalStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
      protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
      (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      verifyMacResultAt x.ret
        (x.msg.verifyMacWithAddresses F
          (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
          x.senderIk x.receiverIk x.macKey) ∗
      macLsLogOff ∗
      A.pool lim (M.stepEvents (verifyMacWithAddressesEvents F parse x) st) sf ∗
      stackAt s0.sp totalStack

abbrev verifyMacWithAddressesPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) (parse : UuidParser) :
    Spec (VerifyMacWithAddressesGhost × M.σ) :=
  verifyMacWithAddressesPlacedSpecWithStack M A lim F parse verifyMacWithAddressesStack

abbrev verifyMacWithAddressesPlacedSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) (parse : UuidParser) :
    Spec (VerifyMacWithAddressesGhost × M.σ) :=
  verifyMacWithAddressesPlacedSpecWithStack M A lim F parse verifyMacWithAddressesStackX

abbrev verifyMacWithAddressesPlacedBudgetSpecWithStack := @verifyMacWithAddressesPlacedSpecWithStack
abbrev verifyMacWithAddressesPlacedBudgetSpec := @verifyMacWithAddressesPlacedSpec
abbrev verifyMacWithAddressesPlacedBudgetSpecX := @verifyMacWithAddressesPlacedSpecX

end LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
